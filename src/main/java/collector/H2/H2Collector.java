package collector.H2;

import collector.Collector;
import history.History;
import lombok.SneakyThrows;

import java.sql.Statement;
import java.util.ArrayList;
import java.util.Properties;
import java.util.concurrent.Callable;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
public class H2Collector extends Collector<Long, Long> {
    public static final String NAME = "H2";

    static {
        try {
            Class.forName("org.h2.Driver");
        } catch (ClassNotFoundException e) {
            throw new RuntimeException(e);
        }
    }

    @SneakyThrows
    public H2Collector(Properties config) {
        super(config);
    }

    @Override
    @SneakyThrows
    public History<Long, Long> collect(History<Long, Long> history) {
        createTable();
        createVariables(nKey);
        ExecutorService executor = Executors.newFixedThreadPool(history.getSessions().size());
        var todo = new ArrayList<Callable<Void>>();
        history.getSessions().values().forEach(session -> {
            Callable<Void> task = () -> {
                var node = new H2Client(url, username, password);
                node.execSession(session, isolation);
                node.close();
                session.getTransactions().removeIf((txn) -> !txn.isSuccess());
                return null;
            };
            todo.add(task);
        });
        executor.invokeAll(todo);
        dropDatabase();
        history.getSessions().values().forEach(session -> session.getTransactions().removeIf(txn -> !txn.isSuccess()));
        history.getSessions().entrySet().removeIf(entry -> entry.getValue().getTransactions().isEmpty());
        history.getTransactions().entrySet().removeIf((entry) -> !entry.getValue().isSuccess());
        return history;
    }

    @Override
    @SneakyThrows
    protected void createTable() {
        var statement = connection.createStatement();
        statement.executeUpdate("CREATE SCHEMA IF NOT EXISTS dbtest");
        statement.executeUpdate("DROP TABLE IF EXISTS dbtest.variables");
        statement.executeUpdate("CREATE TABLE IF NOT EXISTS dbtest.variables (var BIGINT NOT NULL PRIMARY KEY, val BIGINT NOT NULL)");
    }

    @Override
    @SneakyThrows
    protected void createVariables(long nKey) {
        var insertStmt = connection.prepareStatement("INSERT INTO dbtest.variables (var, val) values (?, 0)");
        for (long k = 1; k <= nKey; k++) {
            insertStmt.setLong(1, k);
            insertStmt.addBatch();
        }
        insertStmt.executeBatch();
    }

    @Override
    @SneakyThrows
    protected void dropDatabase() {
        Statement statement = connection.createStatement();
        statement.executeUpdate("DROP SCHEMA IF EXISTS dbtest CASCADE");
    }
}
