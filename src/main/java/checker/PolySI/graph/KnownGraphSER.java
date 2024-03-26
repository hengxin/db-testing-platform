package checker.PolySI.graph;


import com.google.common.graph.MutableValueGraph;
import com.google.common.graph.ValueGraphBuilder;
import history.History;
import history.Transaction;
import lombok.Getter;
import org.apache.commons.lang3.tuple.Pair;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;

import static history.Operation.Type.READ;
import static history.Operation.Type.WRITE;

@SuppressWarnings("UnstableApiUsage")
@Getter
public class KnownGraphSER<KeyType, ValueType> {
    private final MutableValueGraph<Transaction<KeyType, ValueType>, Collection<Edge<KeyType>>> readFrom = ValueGraphBuilder
            .directed().build();
    private final MutableValueGraph<Transaction<KeyType, ValueType>, Collection<Edge<KeyType>>> knownGraph = ValueGraphBuilder
            .directed().build();

    /**
     * Build a graph from a history
     *
     * The built graph contains SO and WR edges
     */
    public KnownGraphSER(History<KeyType, ValueType> history) {
        history.getTransactions().values().forEach(txn -> {
            knownGraph.addNode(txn);
            readFrom.addNode(txn);
        });

        // add SO edges
        history.getSessions().values().forEach(session -> {
            Transaction<KeyType, ValueType> prevTxn = null;
            for (var txn : session.getTransactions()) {
                if (prevTxn != null) {
                    addEdge(knownGraph, prevTxn, txn,
                            new Edge<>(EdgeType.SO, null));
                }
                prevTxn = txn;
            }
        });

        // add WR edges
        var writes = new HashMap<Pair<KeyType, ValueType>, Transaction<KeyType, ValueType>>();
        var events = history.getOperations();

        events.stream().filter(e -> e.getType() == WRITE).forEach(ev -> writes
                .put(Pair.of(ev.getKey(), ev.getValue()), ev.getTransaction()));

        events.stream().filter(e -> e.getType() == READ).forEach(ev -> {
            var writeTxn = writes.get(Pair.of(ev.getKey(), ev.getValue()));
            var txn = ev.getTransaction();

            if (writeTxn == txn) {
                return;
            }

            putEdge(writeTxn, txn, new Edge<KeyType>(EdgeType.WR, ev.getKey()));
        });
    }

    public void putEdge(Transaction<KeyType, ValueType> u,
            Transaction<KeyType, ValueType> v, Edge<KeyType> edge) {
//        System.out.println("put edge " + u.getId() + " " + v.getId() + " " + edge);
        switch (edge.getType()) {
        case WR:
            addEdge(readFrom, u, v, edge);
            // fallthrough
        case WW:
        case SO:
        case RW:
            addEdge(knownGraph, u, v, edge);
            break;
        }
    }

    public void removeEdge(Transaction<KeyType, ValueType> u, Transaction<KeyType, ValueType> v, Edge<KeyType> edge) {
        switch (edge.getType()) {
            case WR:
                removeEdge(readFrom, u, v, edge);
                // fallthrough
            case WW:
            case SO:
            case RW:
                removeEdge(knownGraph, u, v, edge);
                break;
        }
    }

    private void addEdge(
            MutableValueGraph<Transaction<KeyType, ValueType>, Collection<Edge<KeyType>>> graph,
            Transaction<KeyType, ValueType> u,
            Transaction<KeyType, ValueType> v, Edge<KeyType> edge) {
        if (!graph.hasEdgeConnecting(u, v)) {
            graph.putEdgeValue(u, v, new ArrayList<>());
        }
        if (graph.edgeValue(u, v).get().contains(edge)) {
            return;
        }
        graph.edgeValue(u, v).get().add(edge);
    }

    private void removeEdge(
            MutableValueGraph<Transaction<KeyType, ValueType>, Collection<Edge<KeyType>>> graph,
            Transaction<KeyType, ValueType> u,
            Transaction<KeyType, ValueType> v, Edge<KeyType> edge) {
        if (!graph.hasEdgeConnecting(u, v)) {
            return;
        }
        graph.edgeValue(u, v).get().removeIf(e -> e.equals(edge));
        if (graph.edgeValue(u, v).get().isEmpty()) {
            graph.removeEdge(u, v);
        }
    }
}
