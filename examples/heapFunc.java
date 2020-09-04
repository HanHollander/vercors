final class Heap {
    int[] buffer;

    //@ requires 0 <= i;
    //@ ensures 0 <= \result;
    //@ ensures i != 0 ==> (i == childIndex(\result, true) || i == childIndex(\result, false));
    private static /*@ pure @*/ int parentIndex(int i) {
        if (i == 0) {
            return 0;
        } else {
            return (i - 1) / 2;
        }
    }

    //@ requires 0 <= i;
    private static /*@ pure @*/ boolean hasChild(int i, int length, boolean leftChild) {
        return childIndex(i, leftChild) < length;
    }

    //@ requires 0 <= i;
    //@ ensures i < \result;
    private static /*@ pure @*/ int childIndex(int i, boolean leftChild) {
        if (leftChild) {
            return i * 2 + 1;
        } else {
            return i * 2 + 2;
        }
    }

    //@ requires 0 <= other;
    //@ ensures 0 <= \result;
    //@ ensures \result == childIndex(parentIndex(other), false) || \result == childIndex(parentIndex(other), true);
    private static /*@ pure @*/ int getSiblingIndex(int other) {
        int parent = parentIndex(other);
        if (parent * 2 + 1 == other) {
            return parent * 2 + 2;
        } else {
            return parent * 2 + 1;
        }
    }

    /*@ requires 0 <= i && i < |xs|;
        ensures |\result| == |xs|;
        ensures (\forall int k = 0 .. |xs|; i != k ==> {: \result[k] :} == xs[k]);
        ensures \result[i] == v;
        private static seq<int> updateSeq(seq<int> xs, int i, int v) = i > 0
            ? seq<int>{ head(xs) } + updateSeq(tail(xs), i - 1, v)
            : seq<int>{ v } + tail(xs);
     @*/

    /*@
        requires xs != null;
        requires Perm(xs[*], read);
        requires 0 <= j && j < xs.length;
        private static bool isSubHeap(int[] xs, int j) =
            (\let int left = childIndex(j, true);
            (\let int right = childIndex(j, false);
            (left < xs.length ==>
                xs[j] >= xs[left] && isSubHeap(xs, left))
            &&
            (right < xs.length ==>
                xs[j] >= xs[right] && isSubHeap(xs, right))));
     @*/

    /*@
        requires xs != null;
        requires Perm(xs[*], read);
        requires 0 <= j && j < xs.length;
        private static bool isSubHeapSkip(int[] xs, int j, int freshIndex) =
            (\let int left = childIndex(j, true);
            (\let int right = childIndex(j, false);
            (left < xs.length ==>
                (freshIndex != left ==> xs[j] >= xs[left])
                && isSubHeapSkip(xs, left, freshIndex))
            &&
            (right < xs.length ==>
                (freshIndex != right ==> xs[j] >= xs[right])
                && isSubHeapSkip(xs, right, freshIndex))));
     @*/

    /*@
    given frac P;
    context 0 < P && P < write;
    context xs != null ** Perm(xs[*], P);
    context ys != null ** Perm(ys[*], P);
    context ys.length == xs.length + 1;
    context (\forall int i = 0 .. xs.length; xs[i] == ys[i]);
    requires 0 <= j && j < xs.length;
    requires isSubHeap(xs, j);
    ensures isSubHeapSkip(ys, j, xs.length);
    ghost private void lemmaSubHeapToSubHeapSkip(int[] xs, int[] ys, int j) {
        int left = childIndex(j, true);
        int right = childIndex(j, false);
        int freshIndex = xs.length;

        if (left < xs.length) {
            assert isSubHeap(xs, left);
            lemmaSubHeapToSubHeapSkip(xs, ys, left) with { P = P \ 2; };
            assert isSubHeapSkip(ys, left, xs.length);
            assert freshIndex != left;
            assert xs[j] >= xs[left];
        }

        if (right < xs.length) {
            assert isSubHeap(xs, right);
            lemmaSubHeapToSubHeapSkip(xs, ys, right) with { P = P \ 2; };
            assert isSubHeapSkip(ys, right, xs.length);
            assert freshIndex != right;
            assert xs[j] >= xs[right];
        }

        // The following two asserts are needed:
        assert (left < ys.length ==>
                (freshIndex != left ==> ys[j] >= ys[left])
                && isSubHeapSkip(ys, left, freshIndex));
        assert (right < ys.length ==>
                (freshIndex != right ==> ys[j] >= ys[right])
                && isSubHeapSkip(ys, right, freshIndex));
        // Now the main postcondition can be asserted:
        assert isSubHeapSkip(ys, j, freshIndex);
    }
     @*/


    //@ requires Perm(buffer, 1\2) ** buffer != null ** Perm(buffer[*], write);
    //@ requires buffer.length > 0 ==> isSubHeap(buffer, 0);
    void insert(int x) {
        int[] newBuffer = new int[buffer.length + 1];
        int i;

        //@ loop_invariant Perm(newBuffer[*], write);
        //@ loop_invariant Perm(buffer, 1\2) ** buffer != null ** Perm(buffer[*], 1\2);
        //@ loop_invariant 0 <= i && i <= buffer.length;
        //@ loop_invariant newBuffer.length == buffer.length + 1;
        //@ loop_invariant (\forall int j = 0 .. i; newBuffer[j] == buffer[j]);
        for (i = 0; i < buffer.length; i++) {
            newBuffer[i] = buffer[i];
        }

        newBuffer[buffer.length] = x;

        if (newBuffer.length == 1) {
            // Already sorted
            //@ assert isSubHeap(newBuffer, 0);
        } else {
            //@ assert buffer.length > 0;
            //@ assert isSubHeap(buffer, 0);
            //@ assert newBuffer.length > 1;
            //@ ghost lemmaSubHeapToSubHeapSkip(buffer, newBuffer, 0) with { P = 1 \ 4; };
            //@ assert isSubHeapSkip(newBuffer, 0, newBuffer.length - 1);
        }
    }
}