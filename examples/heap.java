final class Heap {
    int[] buffer;

    //@ requires 0 <= i;
    //@ ensures 0 <= \result;
    private static /*@ pure @*/ int parentIndex(int i) {
        if (i == 0) {
            return 0;
        } else {
            return (i - 1) / 2;
        }
    }

    /*@ static resource arrIsHeapSkip(int[] xs, seq<int> elems, int skip) = xs != null ** Perm(xs[*], write)
            ** |elems| == xs.length
            ** (\forall int i = 0 .. xs.length; elems[i] == xs[i])
            ** (\forall int i = 0 .. xs.length; i != skip ==> xs[parentIndex(i)] >= xs[i]);
     @*/

    /*@ static resource arrIsHeap(int[] xs, seq<int> elems) = xs != null ** Perm(xs[*], write)
            ** |elems| == xs.length
            ** (\forall int i = 0 .. xs.length; elems[i] == xs[i])
            ** (\forall int i = 0 .. xs.length; xs[parentIndex(i)] >= xs[i]);
     @*/

    /*@ requires 0 <= i && i < |xs|;
        ensures |\result| == |xs|;
        ensures (\forall int k = 0 .. |xs|; i != k ==> \result[k] == xs[k]);
        ensures \result[i] == v;
        private static seq<int> updateSeq(seq<int> xs, int i, int v) = i > 0
            ? seq<int>{ head(xs) } + updateSeq(tail(xs), i - 1, v)
            : seq<int>{ v } + tail(xs);
     @*/

    //@ resource heapInv(seq<int> elems) = Perm(buffer, write) ** arrIsHeap(buffer, elems);

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

        //@ fold arrIsHeapSkip(newBuffer, newElems, newBuffer.length - 1);
        // assert arrIsHeapSkip(newBuffer, newElems, newBuffer.length - 1);

        i = newBuffer.length - 1;
        //@ unfold arrIsHeapSkip(newBuffer, newElems, newBuffer.length - 1);
        boolean p = !(newBuffer[parentIndex(i)] >= newBuffer[i]);
        //@ fold arrIsHeapSkip(newBuffer, newElems, newBuffer.length - 1);

        //@ loop_invariant 0 <= i && i < newBuffer.length;
        //@ loop_invariant arrIsHeapSkip(newBuffer, newElems, i);
        /*@ loop_invariant p == \unfolding arrIsHeapSkip(newBuffer, newElems, i)
                \in !(newBuffer[parentIndex(i)] >= newBuffer[i]);
          @*/
//        while (!(newBuffer[parentIndex(i)] >= newBuffer[i])) {
        while (p) {
            // assert false;
            /*
            // unfold arrIsHeapSkip(newBuffer, newElems, i);

            // assert false;

            int v1 = newBuffer[i];
            int v2 = newBuffer[parentIndex(i)];
            newBuffer[i] = v2;
            newBuffer[parentIndex(i)] = v1;
            // ghost newElems = updateSeq(updateSeq(elems, i, v2), parentIndex(i), v1);

            // fold arrIsHeapSkip(newBuffer, newElems, parentIndex(i));
            // inhale false;
             */

//            i = parentIndex(i);
            //@ unfold arrIsHeapSkip(newBuffer, newElems, newBuffer.length - 1);
            boolean p = !(newBuffer[parentIndex(i)] >= newBuffer[i]);
            //@ fold arrIsHeapSkip(newBuffer, newElems, newBuffer.length - 1);
        }

        //@ assert !p;
        /*@ assert \unfolding arrIsHeapSkip(newBuffer, newElems, i)
                \in (newBuffer[parentIndex(i)] >= newBuffer[i]);
         @*/

        // inhale false;

        // unfold arrIsHeapSkip(newBuffer, newElems, i);
        // fold arrIsHeap(newBuffer, newElems);
        buffer = newBuffer;
        // assert arrIsHeap(buffer, newElems);

    }
}