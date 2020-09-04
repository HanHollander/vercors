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

    /*@ static inline resource arrIsHeapSkip(int[] xs, seq<int> elems, int skip) = xs != null ** Perm(xs[*], write)
            ** |elems| == xs.length
            ** (\forall int j = 0 .. xs.length; elems[j] == xs[j])
            ** (\forall int j = 0 .. xs.length; j != skip ==> {: xs[parentIndex(j)] :} >= xs[j]);
     @*/

    /*@ static resource arrIsHeap(int[] xs, seq<int> elems) = xs != null ** Perm(xs[*], write)
            ** |elems| == xs.length
            ** (\forall int i = 0 .. xs.length; elems[i] == xs[i])
            ** (\forall int i = 0 .. xs.length; {: xs[parentIndex(i)] :} >= xs[i]);
     @*/

    /*@ requires 0 <= i && i < |xs|;
        ensures |\result| == |xs|;
        ensures (\forall int k = 0 .. |xs|; i != k ==> {: \result[k] :} == xs[k]);
        ensures \result[i] == v;
        private static seq<int> updateSeq(seq<int> xs, int i, int v) = i > 0
            ? seq<int>{ head(xs) } + updateSeq(tail(xs), i - 1, v)
            : seq<int>{ v } + tail(xs);
     @*/

    //@ resource heapInv(seq<int> elems) = Perm(buffer, write) ** arrIsHeap(buffer, elems);

    /*@
        requires xs != null;
        requires Perm(xs[*], read);
        requires 0 <= j && j < xs.length;
        private static bool isSubHeap(int[] xs, int j) =
            (hasChild(xs.length, j, true) ==>
                xs[j] >= xs[childIndex(j, true)] && isSubHeap(xs, childIndex(j, true)))
            &&
            (hasChild(xs.length, j, false) ==>
                xs[j] >= xs[childIndex(j, false)] && isSubHeap(xs, childIndex(j, false)));
     @*/

    /*@
    context [1\4]arrIsHeapSkip(xs, elems, freshIndex);
    requires 0 <= freshIndex && freshIndex < xs.length;
    requires freshIndex <= j && j < xs.length;
    ensures isSubHeap(xs, j);
    ghost private static void lemmaIsSubHeap(int[] xs, seq<int> elems, int freshIndex, int j) {
        // Left child
        if (hasChild(j, xs.length, true)) {
            lemmaIsSubHeap(xs, elems, freshIndex, childIndex(j, true));
            assert isSubHeap(xs, childIndex(j, true));
        }
        // Right child
        if (hasChild(j, xs.length, false)) {
            lemmaIsSubHeap(xs, elems, freshIndex, childIndex(j, false));
            assert isSubHeap(xs, childIndex(j, false));
        }
    }
    @*/

    /*@
    context [1\4]arrIsHeapSkip(xs, elems, freshIndex);
    requires 0 <= freshIndex && freshIndex < xs.length;
    requires getSiblingIndex(freshIndex) == j;
    requires 0 <= j && j < xs.length;
    ensures isSubHeap(xs, j);
    ghost private static void lemmaIsSubHeapSibling(int[] xs, seq<int> elems, int freshIndex, int j) {
        // Left child
        if (hasChild(j, xs.length, true)) {
            lemmaIsSubHeap(xs, elems, freshIndex, childIndex(j, true));
            assert isSubHeap(xs, childIndex(j, true));
        }
        // Right child
        if (hasChild(j, xs.length, false)) {
            lemmaIsSubHeap(xs, elems, freshIndex, childIndex(j, false));
            assert isSubHeap(xs, childIndex(j, false));
        }
    }
    @*/

    /*@
    context [1\2]arrIsHeapSkip(xs, xsElems, freshIndex);
    requires 0 <= freshIndex && freshIndex < xs.length;
    requires xs[parentIndex(freshIndex)] < xs[freshIndex];
    ensures [1\2]arrIsHeapSkip(ys, ysElems, parentIndex(freshIndex));
    ghost void lemmaHeapSkipSwap(int[] xs, seq<int> xsElems, int[] ys, seq<int> ysElems, int freshIndex) {
        int parentFreshIndex = parentIndex(freshIndex);

        // If freshIndex == 0, the < requires does not hold
        assert freshIndex != parentFreshIndex;
        assert 0 <= parentFreshIndex && parentFreshIndex < freshIndex;

        int siblingIndex = getSiblingIndex(freshIndex);

        lemmaIsSubHeap(xs, xsElems, freshIndex, freshIndex);
        assert isSubHeap(xs, freshIndex);

        if (siblingIndex < xs.length) {
            lemmaIsSubHeapSibling(xs, xsElems, freshIndex, siblingIndex);
            assert isSubHeap(xs, siblingIndex);
        }

        assert xs[parentIndex(freshIndex)] < xs[freshIndex];
        // Implies (in my opinion, not yet proven):
        assert isSubHeap(ys, parentFreshIndex);

        assert [1\2]arrIsHeapSkip(ys, ysElems, parentFreshIndex);
    }
    @*/

    /*@
    context xs != null ** Perm(xs[*], 1\2) ** xs.length > 0;
    requires 0 <= j && j < xs.length;
    requires isSubHeap(xs, j);
    ensures (\forall int i = j .. xs.length; {: xs[parentIndex(i)] :} >= xs[i]);
    ghost void lemmaSubheapImpliesIsHeap(int[] xs, int j) {
        if (hasChild(xs.length, j, false)) {
            lemmaSubheapImpliesIsHeap(xs, childIndex(j, false));
        }
        if (hasChild(xs.length, j, true)) {
            lemmaSubheapImpliesIsHeap(xs, childIndex(j, true));
        }
    }
     @*/

    //@ given seq<int> elems;
    //@ requires heapInv(elems);
    void insert(int x) {
        //@ unfold heapInv(elems);
        //@ unfold arrIsHeap(buffer, elems);

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
        //@ ghost seq<int> newElems = elems + seq<int>{x};

        //@ assert arrIsHeapSkip(newBuffer, newElems, newBuffer.length - 1);

        int newIndex = newBuffer.length - 1;

        //@ loop_invariant 0 <= newIndex && newIndex < newBuffer.length;
        //@ loop_invariant arrIsHeapSkip(newBuffer, newElems, newIndex);
        while ((!(newBuffer[parentIndex(newIndex)] >= newBuffer[newIndex]))) {
            //@ assert newBuffer[parentIndex(newIndex)] < newBuffer[newIndex];
            /*@ assert (\forall int j = 0 .. newBuffer.length;
                            j != newIndex ==> {: newBuffer[parentIndex(j)] :} >= newBuffer[j]); @*/

            int insertedValue = newBuffer[newIndex];
            int oldValue = newBuffer[parentIndex(newIndex)];
            newBuffer[newIndex] = oldValue;
            newBuffer[parentIndex(newIndex)] = insertedValue;
            //@ assert newBuffer[parentIndex(newIndex)] >= newBuffer[newIndex];

            /*@ ghost newElems = updateSeq(
                    updateSeq(newElems, newIndex, oldValue), parentIndex(newIndex), insertedValue); @*/
            //@ assert newElems[parentIndex(newIndex)] >= newElems[newIndex];

            /*@ assert (\forall int j = 0 .. newBuffer.length;
                            j != parentIndex(newIndex) ==> {: newBuffer[parentIndex(j)] :} >= newBuffer[j]); @*/

            newIndex = parentIndex(newIndex);
            //@ assert (\forall int j = 0 .. newBuffer.length; newElems[j] == newBuffer[j]);
            /*@ assert (\forall int j = 0 .. newBuffer.length;
                            j != newIndex ==> {: newBuffer[parentIndex(j)] :} >= newBuffer[j]); @*/
            //@ assert false;
            //@ assert arrIsHeapSkip(newBuffer, newElems, newIndex);
        }

        //@ assert false;

        //@ assert arrIsHeapSkip(newBuffer, newElems, i);
        //@ assert newBuffer[parentIndex(i)] >= newBuffer[i];
        //@ fold arrIsHeap(newBuffer, newElems);
        buffer = newBuffer;
        //@ assert arrIsHeap(buffer, newElems);
    }
}