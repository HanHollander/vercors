final class Heap {
    int[] buffer;

    //@ requires 0 <= i;
    //@ ensures \result >= 0;
    //@ ensures \result <= i;
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
            ** (\forall int i = 0 .. xs.length; i != skip ==> {: xs[parentIndex(i)] :} >= xs[i]);
     @*/

    /*@ static resource arrIsHeap(int[] xs, seq<int> elems) = xs != null ** Perm(xs[*], write)
            ** |elems| == xs.length
            ** (\forall int i = 0 .. xs.length; elems[i] == xs[i])
            ** (\forall int i = 0 .. xs.length; {: xs[parentIndex(i)] :} >= xs[i]);
     @*/

    //@ given seq<int> elems;
    //@ requires Perm(buffer, write);
    //@ requires arrIsHeap(buffer, elems);
    void insert(int x) {
        //@ unfold arrIsHeap(buffer, elems);

        int[] newBuffer = new int[buffer.length + 1];

        //@ inhale (\forall int j = 0 .. buffer.length; newBuffer[j] == buffer[j]);

        newBuffer[buffer.length] = x;
        //@ ghost seq<int> newElems = elems + seq<int>{x};

        //@ fold arrIsHeapSkip(newBuffer, newElems, newBuffer.length - 1);

        int i = newBuffer.length - 1;
        //@ assert Perm(newBuffer[i], write);
    }
}