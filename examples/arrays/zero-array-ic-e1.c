// -*- tab-width:2 ; indent-tabs-mode:nil -*-
//:: cases zero-array-c-err
//:: tools silicon
//:: verdict Fail

/*@
  invariant ar != NULL && \length(ar)==len;
  context  (\forall* int i;0<=i && i < len;Perm(ar[i],write));
  ensures  (\forall int k ; 0 <= k && k < len ; ar[k]==0 );
@*/
void zero_array(int ar[],int len){
    //@ assert \length(ar)==len ;
    for(int i=0;i < len;i++)
       /*@  context Perm(ar[i],write);
            ensures ar[i]==0;
       @*/
    {
        ar[i]=2;
    }
}


