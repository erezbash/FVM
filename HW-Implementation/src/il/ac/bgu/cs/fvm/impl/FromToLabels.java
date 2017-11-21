package il.ac.bgu.cs.fvm.impl;

import java.util.Set;

class FromToLabels<STATE, ATOMIC_PROPOSITION> {
    STATE from;
    Set<ATOMIC_PROPOSITION> labels;

    public FromToLabels(STATE from, Set<ATOMIC_PROPOSITION> labels) {
        this.from = from;
        this.labels = labels;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (!(o instanceof FromToLabels)) return false;

        FromToLabels<?, ?> that = (FromToLabels<?, ?>) o;

        return from.equals(that.from) && labels.equals(that.labels);
    }

    @Override
    public int hashCode() {
        int result = from.hashCode();
        result = 31 * result + labels.hashCode();
        return result;
    }
}