package checker.C4;

import checker.Checker;
import checker.IsolationLevel;
import history.History;

import checker.C4.badPattern.BadPatternType;
import checker.C4.graph.*;
import history.Operation;
import history.Transaction;
import javafx.util.Pair;
import lombok.Data;

import java.util.*;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicInteger;

@Data
public class C4<KeyType, ValType> implements Checker<KeyType, ValType> {
    private History<KeyType, ValType> history;

    private final Set<BadPatternType> badPatterns = new HashSet<>();
    private final Map<String, Integer> badPatternCount = new HashMap<>();
    private final Graph<KeyType, ValType> graph = new Graph<>();

    private final Map<Pair<KeyType, ValType>, Operation<KeyType, ValType>> writes = new HashMap<>();
    private final Map<Pair<KeyType, ValType>, List<Operation<KeyType, ValType>>> reads = new HashMap<>();
    private final Map<Pair<KeyType, ValType>, List<Operation<KeyType, ValType>>> readsWithoutWrites = new HashMap<>();
    private final Map<KeyType, Set<Node<KeyType, ValType>>> writeNodes = new HashMap<>();
    private final Map<KeyType, Set<Pair<Node<KeyType, ValType>, Node<KeyType, ValType>>>> WREdges = new HashMap<>();
    private final Map<Operation<KeyType, ValType>, Node<KeyType, ValType>> op2node = new HashMap<>();
    private final Set<Operation<KeyType, ValType>> internalWrites = new HashSet<>();

    private static final Long ZERO = 0L;

    public static final String NAME = "C4";
    public static IsolationLevel ISOLATION_LEVEL;

    public C4(Properties config) {
        ISOLATION_LEVEL = IsolationLevel.valueOf(config.getProperty("db.isolation"));
    }

    @Override
    public boolean verify(History<KeyType, ValType> history) {
        this.history = history;
        buildCO();
        checkCOBP();
        if (ISOLATION_LEVEL == IsolationLevel.READ_COMMITTED) {
            return !badPatternCount.isEmpty();
        }
        syncClock();
        buildVO();
        if (!hasCircle(Edge.Type.VO)) {
            return !badPatternCount.isEmpty();
        }
        checkVOBP();
        return !badPatternCount.isEmpty();
    }

    private void buildCO() {
        var hist = history.getFlatTransactions();
        Map<Long, Node<KeyType, ValType>> prevNodes = new HashMap<>();

        for (var txn: hist) {
            if (!txn.isSuccess()) {
                continue;
            }
            // update node with prev node
            var prev = prevNodes.get(txn.getSession().getId());
            var node = constructNode(txn, prev);
            graph.addVertex(node);
            prevNodes.put(txn.getSession().getId(), node);
            if (prev != null) {
                graph.addEdge(prev, node, new Edge<>(Edge.Type.SO, null));
            }

            var nearestRW = new HashMap<KeyType, Operation<KeyType, ValType>>();
            var writesInTxn = new HashMap<KeyType, Operation<KeyType, ValType>>();

            for (var op: txn.getOps()) {
                var key = new Pair<>(op.getKey(), op.getValue());
                op2node.put(op, node);

                // if op is a read
                if (op.getType() == Operation.Type.READ) {

                    // check NonRepeatableRead and NotMyOwnWrite
                    var prevRW = nearestRW.get(op.getKey());
                    if (prevRW != null && !op.getValue().equals(prevRW.getValue())) {
                        if (prevRW.getType() == Operation.Type.READ) {
                            findBadPattern(BadPatternType.NonRepeatableRead);
                        } else {
                            findBadPattern(BadPatternType.NotMyOwnWrite);
                        }
                    }
                    nearestRW.put(op.getKey(), op);

                    var write = writes.get(key);
                    if (write != null) {
                        // if write -> op
                        // add op to reads
                        reads.computeIfAbsent(key, k -> new ArrayList<>()).add(op);

                        var writeNode = op2node.get(write);
                        if (!writeNode.equals(node)) {
                            if (!writeNode.canReachByCO(node)) {
                                node.updateCOReachability(writeNode);
                                graph.addEdge(writeNode, node, new Edge<>(Edge.Type.WR, op.getKey()));
                            }
                            WREdges.computeIfAbsent(op.getKey(), k -> new HashSet<>()).add(new Pair<>(writeNode, node));
                        }
                    } else if (op.getValue().equals(ZERO)) {
                        // if no write -> op, but op reads zero
                        reads.computeIfAbsent(key, k -> new ArrayList<>()).add(op);
                    } else {
                        readsWithoutWrites.computeIfAbsent(key, k -> new ArrayList<>()).add(op);
                    }
                } else {
                    // if op is write
                    writes.put(key, op);
                    writeNodes.computeIfAbsent(op.getKey(), k -> new HashSet<>()).add(node);

                    nearestRW.put(op.getKey(), op);

                    // check internal write
                    var internalWrite = writesInTxn.get(op.getKey());
                    if (internalWrite != null) {
                        internalWrites.add(internalWrite);
                    }
                    writesInTxn.put(op.getKey(), op);

                    var pendingReads = readsWithoutWrites.get(key);
                    if (pendingReads != null) {
                        reads.computeIfAbsent(key, k -> new ArrayList<>()).addAll(pendingReads);
                        for (var pendingRead: pendingReads) {
                            var pendingReadNode = op2node.get(pendingRead);
                            if (!node.equals(pendingReadNode)) {
                                graph.addEdge(node, pendingReadNode, new Edge<>(Edge.Type.WR, op.getKey()));
                                WREdges.computeIfAbsent(op.getKey(), k -> new HashSet<>()).add(new Pair<>(node, pendingReadNode));
                            }
                        }
                    }
                    readsWithoutWrites.remove(key);
                }
            }
            updateVec(new HashSet<>(), node, node, Edge.Type.CO);
        }
    }

    private void checkCOBP() {
        // check aborted read and thin air
        if (!readsWithoutWrites.isEmpty()) {
            AtomicInteger count = new AtomicInteger();
            readsWithoutWrites.keySet().forEach((key) -> {
                if (history.getAbortedWrites().contains(key)) {
                    // find aborted read
                    findBadPattern(BadPatternType.AbortedRead);
                    count.addAndGet(1);
                }
            });
            if (count.get() != readsWithoutWrites.size()) {
                // find thin air read
                findBadPattern(BadPatternType.ThinAirRead);
            }
        }

        // for each read
        reads.values().forEach((readList) -> {
            readList.forEach((read) -> {
                var key = new Pair<>(read.getKey(), read.getValue());
                var node = op2node.get(read);

                // read(x, 0)
                if (read.getValue().equals(ZERO)) {
                    var writeRelNodes = writeNodes.get(read.getKey());

                    // no write(x, k)
                    if (writeRelNodes == null) {
                        return;
                    }

                    // check InitialRead if check TCC
                    if (ISOLATION_LEVEL == IsolationLevel.CAUSAL_CONSISTENCY) {
                        // check if write(x, k) co-> read
                        writeRelNodes.forEach((writeNode) -> {
                            if (writeNode.equals(node)) {
                                return;
                            }
                            if (writeNode.canReachByCO(node)) {
                                // find writeCOInitRead
                                findBadPattern(BadPatternType.WriteCOInitRead);
                            }
                        });
                    }
                    return;
                }

                // write wr-> read
                var write = writes.get(key);
                var writeNode = op2node.get(write);

                if (!writeNode.equals(node)) {
                    // in different txn
                    if (internalWrites.contains(write)) {
                        // find intermediate write
                        findBadPattern(BadPatternType.IntermediateRead);
                    }
                } else {
                    // in same txn
                    if (write.getId() > read.getId()) {
                        // find future read
                        findBadPattern(BadPatternType.FutureRead);
                    }
                }
            });
        });

        // check CyclicCO if check TCC
        if (ISOLATION_LEVEL == IsolationLevel.CAUSAL_CONSISTENCY) {
            // iter wr edge (t1 wr-> t2)
            WREdges.forEach((varX, edgesX) -> {
                edgesX.forEach((edge) -> {
                    var t1 = edge.getKey();
                    var t2 = edge.getValue();
                    if (t1.canReachByCO(t2) && t2.canReachByCO(t1)) {
                        // find cyclicCO
                        findBadPattern(BadPatternType.CyclicCO);
                    }
                });
            });
        }
    }

    private void buildVO() {
        var pendingNodes = new HashSet<Node<KeyType, ValType>>();

        WREdges.forEach((variable, edges) -> {
            edges.forEach((edge) -> {
                var t1 = edge.getKey();
                var t2 = edge.getValue();
                writeNodes.get(variable).forEach((t) -> {
                    if (!t.equals(t1) && !(t.equals(t2)) && t.canReachByCO(t2)) {
                        // build vo edge
                        if (t.canReachByCO(t1)) {
                            return;
                        }
                        graph.addEdge(t, t1, new Edge<>(Edge.Type.VO, null));
                        pendingNodes.add(t);
                    }
                });
            });
        });

        // update downstream nodes
        pendingNodes.forEach((node) -> {
            updateVec(new HashSet<>(), node, node, Edge.Type.VO);
        });
    }

    private void checkVOBP() {
        // iter wr edge (t2 wr-> t3)
        WREdges.forEach((varX, edgesX) -> {
            edgesX.forEach((edge) -> {
                var t2 = edge.getKey();
                var t3 = edge.getValue();

                writeNodes.get(varX).forEach((t1) -> {
                    if (!t1.equals(t2) && !t1.equals(t3) && t1.canReachByCO(t3) && t2.canReachByCO(t1)) {
                        // find bp triangle
                        AtomicBoolean isRA = new AtomicBoolean(false);
                        WREdges.forEach((varY, edgesY) -> {
                            if (!varX.equals(varY) && edgesY.contains(new Pair<>(t1, t3))) {
                                isRA.set(true);
                                // find fractured read co
                                findBadPattern(BadPatternType.FracturedReadCO);
                            }
                        });
                        // continue if is RA bp
                        if (isRA.get()) {
                            return;
                        }
                        // check COConflictVO if check TCC, continue if check RA
                        if (ISOLATION_LEVEL == IsolationLevel.CAUSAL_CONSISTENCY) {
                            // find co conflict vo
                            findBadPattern(BadPatternType.COConflictVO);
                        }
                    }
                });
            });
        });

        // iter wr edge (t2 wr-> t3)
        WREdges.forEach((varX, edgesX) -> {
            edgesX.forEach((edge) -> {
                var t2 = edge.getKey();
                var t3 = edge.getValue();

                writeNodes.get(varX).forEach((t1) -> {
                    if (!t1.equals(t2) && !t1.equals(t3) && t1.canReachByCO(t3) && !t2.canReachByCO(t1) && t2.canReachByVO(t1)) {
                        // find bp triangle
                        AtomicBoolean isRA = new AtomicBoolean(false);
                        WREdges.forEach((varY, edgesY) -> {
                            if (!varX.equals(varY) && edgesY.contains(new Pair<>(t1, t3))) {
                                isRA.set(true);
                                // find fractured read vo
                                findBadPattern(BadPatternType.FracturedReadVO);
                            }
                        });
                        // continue if is RA bp
                        if (isRA.get()) {
                            return;
                        }
                        // check ConflictVO if check TCC, continue if check RA
                        if (ISOLATION_LEVEL == IsolationLevel.CAUSAL_CONSISTENCY) {
                            // find conflict vo
                            findBadPattern(BadPatternType.ConflictVO);
                        }
                    }
                });
            });
        });
    }

    private void updateVec(Set<Node<KeyType, ValType>> visited, Node<KeyType, ValType> cur, Node<KeyType, ValType> upNode, Edge.Type edgeType) {
        visited.add(cur);

        var nextNodes = graph.get(cur);
        for (var next: nextNodes) {
            if (edgeType == Edge.Type.CO) {
                if (visited.contains(next) || upNode.canReachByCO(next)) {
                    continue;
                }
                next.updateCOReachability(upNode);
                updateVec(visited, next, upNode, edgeType);
            } else if (edgeType == Edge.Type.VO) {
                if (visited.contains(next) || upNode.canReachByVO(next)) {
                    continue;
                }
                next.updateVOReachability(upNode);
                updateVec(visited, next, upNode, edgeType);
            }
        }
    }

    private void findBadPattern(BadPatternType badPattern) {
        badPatterns.add(badPattern);
        badPatternCount.merge(badPattern.getCode(), 1, Integer::sum);
    }

    private Node<KeyType, ValType> constructNode(Transaction<KeyType, ValType> transaction, Node<KeyType, ValType> prev) {
        short tid = (short) transaction.getSession().getId();
        int dim = history.getSessions().size();
        return new TCNode<>(graph, transaction, tid, dim, prev);
    }

    private void syncClock() {
        graph.getAdjMap().keySet().forEach(Node::syncCOVO);
    }

    private boolean hasCircle(Edge.Type edgeType) {
        return graph.getAdjMap().entrySet().stream().anyMatch((entry) -> {
            var from = entry.getKey();
            var toNodes = entry.getValue();
            return toNodes.stream().anyMatch((node) -> (edgeType == Edge.Type.CO && node.canReachByCO(from)) ||
                    (edgeType == Edge.Type.VO && node.canReachByVO(from)));
        });
    }
}
