method Shor ( a : nat, N : nat, n : nat, x : Q[n], y : Q[n] )
 requires (n > 0)
 requires (1 < a < N)
 requires (N < 2^(n-1))
 requires (gcd(a, N) == 1)
 requires ( type(x) = Tensor n (Nor 0))
 requires ( type(y) = Tensor n (Nor 0))
 ensures (a^xv mod N == yv)
 ensures (gcd(q, t) == 1)
 ensures (is_even(t))
 ensures (a^(t/2) + 1 divides N || a^(t/2) - 1 divides N)
 //ensures (r.pos > (4 * e^(-2) / PI ^ 2) / (Nat.log2 N)^4)
{
  x *= H ;
  y *= cl(y+1); //cl might be omitted.
  for (int i = 0; i < n; x[i]; i ++)
    invariant (0 <= i <= n)
    invariant (saturation(x[0..i]))
    invariant (type(y,x[0..i]) = Tensor n (ch (2^i) {k | j baseof x[0..i] && k = (a^j mod N,j)}))
    invariant ((y,x[0..i]) == psum(k=0,2^i,1,(a^k mod N,k))) //psum(k=b,M,p(k),b(k)) = sum_{k=b}^M p(k)*b(k)
  {
    y *= cl(a^(2^i) * y mod N);
  }

 M z := measure(y);//forall x in x[0..n), valid(x) ==> z.base = a^(x.base) mod N
 x *= RQFT;
 M r := measure(x); //r is r.pos and r.base
 int t := conFrac(r); //continued fraction of r.base and maintain r.pos (probability)
 
}

