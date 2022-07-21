include "../libraries/src/NonlinearArithmetic/DivMod.dfy"
import opened DivMod


lemma A(c : array<int>, n : nat)
  requires c.Length == 2 * n
  requires forall i | 0 <= i < n :: c[i] == 0
  requires forall i | n <= i < 2 * n :: c[i] == 1
  ensures forall i | 0 <= i < n :: c[i + n] == 1
{
  
}

lemma B(c : array<int>, n : nat)
  requires c.Length == 2 * n
  requires forall i | 0 <= i < n :: c[i] == 0
  requires forall i | 0 <= i < n :: c[i + n] == 1
  ensures forall i | 0 <= i < n :: c[i + n] == 1
{
  
}

lemma C(c : array<int>, n : nat)
  requires n > 0;
  requires c.Length == 2 * n
  requires forall i | 0 <= i < n :: c[i] == 0
  requires forall i | 0 <= i < n :: c[i + n] == 1
  ensures forall i | n <= i < n + n :: c[i] == 1
{
  forall i | n <= i < n + n
    ensures c[i] == 1
 {
    assert 0 <= (i - n) < n;
    assert c[(i - n) + n] == 1;
    assert c[i] == 1;
 }
}


lemma Mod(a : nat, b : nat, N : nat)
  requires N > 0
  ensures (a * (b % N)) % N == (a * b) % N
{
  LemmaMulModNoopRightAuto();    
  assert (a * (b % N)) % N == (a * b) % N;
}
