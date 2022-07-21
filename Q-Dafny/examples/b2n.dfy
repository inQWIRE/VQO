module B2N {
  // Array Version
  function method {:opaque} b2nAux(a : array<nat>, i : nat, j : nat) : nat
    reads a
    requires 0 <= i <= j <= a.Length
    requires (forall k | 0 <= k < a.Length :: a[k] == 0 || a[k] == 1)
    decreases j - i
  {
    if i == j then 0 else a[i] + 2 * b2nAux(a, i + 1, j)
  }

  method b2nArray (a : array<nat>) returns (sum : nat)
    requires (forall k | 0 <= k < a.Length :: a[k] == 0 || a[k] == 1)
  {
    sum := b2nAux(a, 0, a.Length);
  }

  lemma LemmaB2NArrayAllZeros(a : array<nat>, i : nat)
    requires 0 <= i <= a.Length
    requires (forall k | 0 <= k < i :: a[k] == 0 || a[k] == 1)
    requires (forall k | i <= k < a.Length :: a[k] == 0)
    ensures b2nAux(a, i, a.Length) == 0
    decreases a.Length - i
  {
    reveal b2nAux();
  }

  lemma LemmaB2NArrayTailingZeros(a : array<nat>, l : nat, i : nat)
    requires 0 <= l <= i <= a.Length
    requires (forall k | 0 <= k < i :: a[k] == 0 || a[k] == 1)
    requires (forall k | i <= k < a.Length :: a[k] == 0)
    ensures b2nAux(a, l, a.Length) == b2nAux(a, l, i)
    decreases i - l
  {
    reveal b2nAux();
    if (i == l) {
      LemmaB2NArrayAllZeros(a, i);
    } 
  }
}

// Sequence Version
/*
function b2n(a : seq<nat>) : nat
  requires (forall k | 0 <= k < |a| :: a[k] == 0 || a[k] == 1)
{
  if |a| == 0 then 0 else a[0] + 2 * b2n(a[1..])
}

lemma LemmaB2NAllZeros(a : seq<nat>)
  requires (forall k | 0 <= k < |a| :: a[k] == 0)
  ensures b2n(a) == 0
{
  
}


lemma LemmaB2NTailingZeros(a : seq<nat>, i : nat)
  requires 0 <= i < |a|
  requires (forall k | 0 <= k < i :: a[k] == 0 || a[k] == 1)
  requires (forall k | i <= k < |a| :: a[k] == 0)
  ensures b2n(a) == b2n(a[0..i])
{
  if (i == 0) {
    LemmaB2NAllZeros(a[i..]);
    assert b2n(a[i..]) == 0;
  } else {
    LemmaB2NTailingZeros(a[1..], i - 1);
    assert b2n(a[1..]) == b2n(a[1..][0..i-1]);
    assert (a[1..][0..i-1] == a[1..i]);
    assert b2n(a[1..]) == b2n(a[1..i]);
    assert a[0] + 2 * b2n(a[1..]) == a[0] + 2 * b2n(a[1..i]);
    assert b2n(a) == b2n(a[0..i]);
  }
}
*/

