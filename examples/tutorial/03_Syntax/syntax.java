// -*- tab-width:4 ; indent-tabs-mode:nil -*-
//:: cases TutorialSyntaxJava
//:: suite TutorialExamples
//:: tools silicon
//:: verdict Pass

/*
    This file contains the Examples from the Chapter "Syntax" of the VerCors tutorial 
    (see https://github.com/utwente-fmt/vercors/wiki/Tutorial-Syntax ).
*/

class Examples {

    /// global variable used by some examples
    int y;


    public void example1() {
        int x = 2;
        //@ assert x == 2;
        int y = x + 3;
        /*@
        assert y == 5;
        @*/
    }
    
    public void example2(int[] arr) {
        /*@
        /// note: currently not supported, see Issue #453
        /// ghost option<int> x = (arr==null ? None : Some(arr.length);
        @*/
    }
    
    /*@
        /// requirements to make assertion actually pass
        requires x==1 && y==5 && z!=null;
    @*/
    public void example3(int x, int y, Object z) {
        //@ assert (\let int abs_x = (x<0 ? -x : x); y==(z==null ? abs_x : 5*abs_x));
    }
    
    /// example 4
    //@ requires arr != null;
    //@ requires Perm(arr[*], read);
    //@ requires (\forall int i ; 0<=i && i<arr.length ; arr[i]>0);
    void foo(int[] arr) {
        /// example of a quantifier using an interval
        //@ assert (\forall int i = 0 .. arr.length ; arr[i]>0);
    }
    
    /// example 5
    //@ requires arr != null;
    //@ requires Perm(arr[*], read);
    //@ requires (\exists int i ; 0<=i && i<arr.length ; arr[i]>0);
    void foo2(int[] arr) {
    }
    
    /*@
        /// requirements to make assertion actually pass
        requires x==4 ** |s| ==1 ** s[0]==2;
    ghost public void example6(int x, seq<int> s) {
        /// Issue #458: \sum not supported
        /// assert x == (\sum int i; 0<i && i<|s|; s[i]*s[i]);
    }
    @*/
    
    public void example7() {
        int x = 2;
        //@ assume x == 1;
        int y = x + 3;
        //@ assert y == 4;
    }
    
    /// example 8
    /*@ 
        context Perm(y, 1);
        requires x == 2;
        ensures y == 5;
    @*/
    public void foo3(int x) {
        y = x + 3;
    }
    
    /// example 9
    //@ requires Perm(y, 1);
    void bar() {
        int a = 2;
        foo3(a);
        a = y + 5;
        //@ assert a == 10;
    }
    
    /// example 10
    //@ context Perm(y, 1\2);
    //@ context y == 5;
    int incr(int x) {
        int res = x + 2*y;
        //@ assert res == x + 10;
        return res;
    }
    
    /// example 11
    //@ context Perm(y, 1\2);
    //@ ensures y == \old(y);
    //@ ensures \result == x + 2*y;
    int incr2(int x) {
        return x + 2*y;
    }
    
    /// example 12
    //@ requires a>0 && b>0;
    //@ ensures \result == a*b;
    public int mult(int a, int b) {
        int res = 0;
        //@ loop_invariant res == i*a;
        //@ loop_invariant i <= b;
        for (int i=0; i<b; i++) {
            res = res+a;
        }
        //@ assert a == \old(a);
        return res;
    }
    
    /// example 13
    /*@
        requires arr != null ** Perm(arr[*], read);
        /// requirements to make assert true
        requires y==5 && arr.length==1 && arr[0]==3;
    @*/
    public void whatever(int x, int y, int[] arr) {
        x = 2;
        //@ ghost int min = (x<y ? x : y);
        //@ assert (\forall int i; 0<=i && i<arr.length; min<=arr[i] && arr[i] < 2*min);
        if (arr.length > 0) {
            x = 4;
        }
        /*@ ghost 
        if (min < x) {
            assert (\forall int i; 0<=i && i<arr.length; min<=arr[i] && arr[i] < 2*min);
        }
        @*/
    }
    
    /// example 14
    /*@
    requires x > 0;
    ensures cond ==> \result == x+y;
    ghost static int cond_add(bool cond, int x, int y) {
        if (cond) {
            return x+y;
        } else {
            return x;
        }
    }
    @*/

    //@ requires val1 > 0 && val2>0 && z==val1+val2;
    void some_method(int val1, int val2, int z) {
        //@ ghost int z2 = cond_add(val2>0, val1, val2);
        //@ assert z == z2;
    }
    
    
    /// example 15
    /*@
    requires x > 0;
    static pure int cond_add2(bool cond, int x, int y) 
        = cond ? x+y : x;
    @*/
    
    /// example 16
    //@ requires a>0 && b>0;
    //@ ensures \result == a*b;
    public int mult2(int a, int b);
    // commented out body for the sake of speeding up the analysis:
    //{
    //  int res = 0;
    //  // loop_invariant res == i*a;
    //  // loop_invariant i <= b;
    //  for (int i=0; i<b; i++) {
    //    res += a;
    //  }
    //  return res;
    //}

    /*@ 
    requires a>0 && b>0;
    ensures \result == a+b;
    public pure int add(int a, int b);
    @*/

    /// example 17
    //@ pure inline int min(int x, int y) = (x<y ? x : y);
    
    /// example 18
    /*@
    given int x;
    given int y2;
    yields int modified_x;
    requires x > 0;
    ensures modified_x > 0;
    @*/
    int some_method2(boolean real_arg) {
        int res = 0;
        /// ...
        //@ ghost modified_x = x + 1;
        /// ...
        return res;
    }

    void other_method2() {
        //@ ghost int some_ghost;
        int some_result = some_method2(true) /*@ with {y2=3; x=2;} then {some_ghost=modified_x;} @*/;
    }
}