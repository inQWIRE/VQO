method Shor (a : int, N : int, n : int, yv : int, x : qubits, y : qubits) returns (xv: int)
  requires (n > 0)
  requires (x.Card > 0)
  requires (y.Card > 0)
  requires (forall i | i >= 0 && i < n :: y[i] == q0)
  ensures (a^xv % N == yv)
{
  x *= H;
  x[0] *= X;
  qfor i := 0 to n
    invariant (i <= n)
    // invariant (forall k | 0 <= k && k < i :: s_sigma(2^i,2*i,(x,y)[k]))
    // invariant (forall k | 0 <=k && k < i :: igma_eq((x,y)[k] == (x,a^(2^sum(j=0,j<i,j))*x[sum(j=0,j<i,j)])[k]))
    // invariant (forall k | i <= k && k < n :: y[k]=q0)
  {
    // classic(a^(2^i) * x[i] mod N);
  }
  // pmeasure(y);
  // x *= QFT;
  // measure(x);
}
