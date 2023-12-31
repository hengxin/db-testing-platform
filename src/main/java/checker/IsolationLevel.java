package checker;

public enum IsolationLevel {
    READ_UNCOMMITTED,
    READ_COMMITTED,
    READ_ATOMICITY,
    REPEATABLE_READ,
    CAUSAL_CONSISTENCY,
    SNAPSHOT_ISOLATION,
    SERIALIZATION
}
