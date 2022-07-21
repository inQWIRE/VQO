include "../libraries/src/NonlinearArithmetic/Power2.dfy"
include "../libraries/src/NonlinearArithmetic/Power.dfy"
include "../libraries/src/NonlinearArithmetic/DivMod.dfy"
include "b2n.dfy"

import opened Power2
import opened Power
import opened B2N
import opened DivMod

lemma LemmaLePow2Covariant(n1 : nat, n2 : nat)
  requires n1 <= n2
  ensures Pow2(n1) <= Pow2(n2)
  decreases n1 + n2
{
  reveal Pow2();
  if n1 == 0
  {
    assert 0 <= Pow2(n2);
  }
  else
  {
    LemmaLePow2Covariant(n1 - 1, n2 - 1);
  }
}

lemma LemmaNLePow2N(n : nat)
  ensures n <= Pow2(n)
{
  reveal Pow2();

  if (n == 0) {
    assert 0 <= Pow2(0);
  } else if (n == 1) {
    assert 1 <= Pow2(1);
  } else {
    LemmaNLePow2N(n - 1);
    assert n - 1 <= Pow2(n - 1);
    assert n <= Pow2(n);
  }
}


datatype Mode =
  | Nor(b : array<nat>)
  | Had(h : array<int>)
  // c : an array of qregister index and phase
  | CH(dof : nat, c : array<(int, int)>)
  
class Qubits {
  var m : Mode;
  var card : nat; 
  
  constructor EmptyCH()
    ensures card == 0
    ensures Wf()
    ensures m.CH?
    ensures m.dof == 1;
    ensures m.c[0] == (0, 1);
  {
    var empty := new (int, int)[1](_ => (0, 1));
    card := 0;
    m := CH(1, empty);
  }

  // Prepare Qubits in Normal Mode
  constructor Prepare0(n : nat)
    requires n > 0;
    ensures card == n && m.Nor?
    ensures m.b.Length == n
    ensures forall i | 0 <= i < n :: m.b[i] == 0
    ensures Wf()
    ensures fresh(m.b)
  {
    card := n;
    var qs := new nat[n](_ => 0);
    m := Nor(qs);
  }

  constructor Prepare1(n : nat)
    requires n > 0;
    ensures card == n && m.Nor?
    ensures m.b.Length == n
    ensures forall i | 0 <= i < n :: m.b[i] == 1
    ensures Wf()
    ensures fresh(m.b)
  {
    card := n;
    var qs := new nat[n](_ => 1);
    m := Nor(qs);
  }

  method SplitPlus(n : nat) returns (q : Qubits)
    requires Wf()
    requires m.Had? 
    requires 0 < n <= card
    ensures q.m.Had? && q.Wf() && q.card == n
    ensures Wf() && m.Had?
    ensures card == old(card) - n && fresh(q)
    // ensures n != old(card) ==> card == old(card) - n && fresh(q)
    // ensures n == old(card) ==> card == n && q == this
    ensures forall k | 0 <= k < n :: q.m.h[k] == old(m.h[k])
    ensures forall k | 0 <= k < m.h.Length :: m.h[k] == old(m.h[k + n])
    // ensures n != old(card) ==> forall k | 0 <= k < m.h.Length :: m.h[k] == old(m.h[k + n])
    modifies this
  {
    var tmpq := new int[n];
    q := new Qubits.Prepare0(n);
    for i := 0 to n
      invariant card == old(card)
      invariant m.Had?
      invariant q.card == n <= card == m.h.Length
      invariant (m.h == old(m.h))
      invariant forall k | 0 <= k < i :: tmpq[k] == m.h[k]
    {
      tmpq[i] := m.h[i];
    }
    q.m := Had(tmpq);
    q.card := n;
    assert q.Wf();
    assert n == q.m.h.Length <= card == m.h.Length;
    var tmp := new int[card - n];
    assert forall k | 0 <= k < n :: q.m.h[k] == old(m.h[k]);
    for i := 0 to (card - n)
      invariant q.Wf() && q.m.Had? && q.card == n
      invariant card == old(card)
      invariant m.Had?
      invariant card == m.h.Length
      invariant tmp.Length == card - n
      invariant i + n <= card
      invariant m.h == old(m.h)
      invariant forall k | 0 <= k < i :: tmp[k] == m.h[k + n]
      invariant forall k | 0 <= k < n :: tmpq[k] == m.h[k];
      invariant tmpq == q.m.h
    {
      tmp[i] := m.h[i + n];
    }
    m := Had(tmp);
    card := tmp.Length;
  }

  predicate WfNor()
    reads this
    reads m.b
    requires m.Nor?
  {
    m.b.Length == card &&
      forall i | 0 <= i < card :: m.b[i] == 0 || m.b[i] == 1
  }
  predicate Wf()
    reads this
  {
    var tmp := Pow2(card);
    // card > 0 &&
    match m {
      case Nor(b) =>
        b.Length == card
      case Had(h) => h.Length == card
      case CH(dof, c) => dof <= tmp && c.Length == dof && dof <= Pow2(card)
    }
  }

  // Apply H to switch Qubits to Hadamard Basis
  method H()
    requires m.Nor?
    requires Wf()
    requires WfNor()
    ensures Wf()
    ensures m.Had?
    ensures m.h.Length == old(m.b.Length) == card
    ensures forall i | 0 <= i < card :: old(m.b[i]) == 0 ==> m.h[i] == 1
    ensures fresh(m.h)
    modifies this
  {
    ghost var tmp := m.b;
    var qs := new int[card];
    var i := 0;
    assert m.Nor?;
    assert qs.Length == m.b.Length == card;
    while i < card
      decreases (card - i)
      invariant m.Nor?
      invariant i <= card
      invariant qs.Length == m.b.Length == card
      invariant forall j | 0 <= j < i :: m.b[j] == 0 ==> qs[j] == 1
      invariant (tmp == m.b);
    {
      qs[i] := if m.b[i] == 0 then 1 else -1;
      i := i + 1;
    }
    assert qs.Length == m.b.Length == card;
    assert (forall i | 0 <= i < card :: m.b[i] == 0 ==> qs[i] == 1);
    m := Had(qs);
  }

  method PlusRetCH()
    requires m.Had?
    requires Wf()
    requires forall i | 0 <= i < card :: m.h[i] == 1
    ensures m.CH?
    ensures m.dof == Pow2(card)
    ensures Wf()
    ensures forall i | 0 <= i < m.dof :: m.c[i] == (i, 1) // amounts to say it's a sum
    ensures fresh(m.c)
    modifies this
  {
    var dof := Pow2(card);
    var c := new (int, int)[dof](i => (i, 1));
    assert (forall i | 0 <= i < dof :: c[i] == (i, 1));
    m := CH(dof, c);
    assert (forall i | 0 <= i < m.dof :: m.c[i] == (i, 1));
  }


  method Xat(i : nat)
    requires m.Nor?
    requires Wf()
    requires WfNor()
    requires 0 <= i < card
    ensures (old(m.b[i]) == 0 && m.b[i] == 1) || (old(m.b[i]) == 1 && m.b[i] == 0)
    ensures (forall k | 0 <= k < m.b.Length :: k != i ==> (m.b[k] == old(m.b[k])))
    ensures m.Nor?
    ensures Wf()
    ensures WfNor()
    modifies m.b
  {
    m.b[i] := 1 - m.b[i];
  }

  method NorRetCH()
    requires m.Nor?
    requires Wf()
    requires WfNor()
    ensures m.CH?
    ensures Wf()
    ensures m.dof == 1
    ensures m.c[0] == (b2nAux(old(m.b), 0, old(m.b.Length)), 1)
    ensures card == old(card)
    modifies this
    ensures fresh(m.c)
  {
    var j := b2nAux(m.b, 0, m.b.Length);
    var t := new (int, int)[1](_ => (j, 1));
    m := CH(1, t);
  }

  method CatPlusCH(q : Qubits)
    requires m.CH? && Wf() && q.m.Had? && q.Wf()
    requires forall i | 0 <= i < m.dof :: m.c[i] == (i, 1)
    requires q.card == 1
    requires q.m.h[0] == 1
    requires m.dof == Pow2(card)
    modifies this
    ensures m.CH? && Wf() && m.dof == 2 * old(m.dof)
    ensures card == old(card) + 1
    ensures fresh(m.c)
    ensures forall i | 0 <= i < m.dof :: m.c[i] == (i, 1)
  {
    reveal Pow2();
    var offset := Pow2(card);
    assert 2 * offset == 2 * m.dof;
    var newH := new (int, int)[2 * m.dof];
    assert 0 <= offset <= newH.Length;
    for i := 0 to m.dof
      invariant card == old(card)
      invariant m.CH? && Wf()
      invariant 0 <= i <= m.dof
      invariant 0 <= i + offset <= newH.Length
      invariant newH.Length == 2 * m.dof
      invariant m.c == old(m.c)
      invariant forall k | 0 <= k < i :: newH[k] == (k, 1)
      invariant forall k | offset <= k < i + offset :: newH[k] == (k, 1)
    {
      newH[i] := m.c[i];
      newH[i + offset] := (offset + m.c[i].0, 1);
    }
    m := CH(2 * offset, newH);
    card := card + 1;
  }
  
  predicate PSumMod(l : nat, r : nat, a : nat, N : nat)
    reads this
    requires N > 0
    requires Wf()
    requires m.CH?
    requires 0 <= l < r <= m.dof
    reads m.c
  {
    forall k | l <= k < r :: (k, Pow(a, k) % N) == m.c[k]
  }

  predicate Saturated()
    requires m.CH?
    requires Wf()
    reads this
    reads m.c
  {
    m.dof == Pow2(card) && forall i | 0 <= i < m.c.Length :: m.c[i] == (i, 1)
  }
}

function method ShorOracle(c : (int, int), i : nat, a : nat , N : nat) : (int, int)
  requires N > 0
{
  ((Pow(a, Pow2(i)) * c.0) % N, c.1)
  // ((Pow(a, Pow2(i)) * c.0) % N, c.1)
}

method ControlledOracle(x : Qubits, y : Qubits, i : nat, a : nat, N : nat)
  returns (oldy : array<(int, int)>)
  // reaction are done in CH modes
  requires N > 0
  requires y.card > 0;
  requires x.m.Had? && y.m.CH?
  requires y.Wf()
  requires y.m.dof <= Pow2(y.card - 1)
  // augment [y] if [i]th qubit in [x] contains 1
  // I may need a lemma saying that if qubits are saturated, then
  // m.c[Pow2(i)] = (Pow2(i), 1)  implies that ith qubits contains 1
  ensures y.Wf()
  ensures y.m.CH? && y.m.dof == 2 * old(y.m.dof)
  ensures y.card == old(y.card)
  ensures forall i | 0 <= i < old(y.m.dof) :: y.m.c[i] == old(y.m.c[i])
  ensures forall j | old(y.m.dof) <= j < y.m.dof ::
    y.m.c[j] == (Pow(a, Pow2(i)) * old(y.m.c[j - y.m.dof].0) % N, old(y.m.c[j - y.m.dof]).1)
  ensures fresh(y.m.c)
  ensures old(y.m.c) == oldy
  modifies y
{
  oldy := y.m.c;
  var newC := new (int, int)[2 * y.m.dof];
  assert y.m.dof == y.m.c.Length;
  var j := 0;
  while j < y.m.dof
    invariant N > 0
    invariant y.m.CH? && y.Wf()
    invariant 0 <= j <= y.m.dof == y.m.c.Length
    invariant 0 <= j + y.m.dof <= newC.Length
    invariant 2 * y.m.dof == newC.Length
    invariant y.card == old(y.card) && y.m.dof == old(y.m.dof) && y.m.c == old(y.m.c)
    invariant forall k | 0 <= k < j :: newC[k] == old(y.m.c[k])
    invariant forall k | 0 <= k < j :: newC[k + y.m.dof] == old(ShorOracle(y.m.c[k], i, a, N))
    decreases y.m.dof - j
  {
    var now := y.m.c[j];
    newC[j] := y.m.c[j];
    newC[j + y.m.dof] := (Pow(a, Pow2(i)) * now.0 % N , now.1);
    j := j + 1;
  }

  y.m := CH(2 * y.m.dof, newC);
  assert y.m.CH? && y.m.dof == 2 * old(y.m.dof);
  reveal Pow2();
  assert y.m.dof <= Pow2(y.card);
}

// Idea :
// Note that when doing qwhile on a qu-register,
// we are reasoning seperately on each quibit inductively/iteratively.
// It's a good idea to encode change of modes on iterator basis?


// React:
// Takes 2 Qubits in CH, abstracted as 
//   forall i | 0 < i < a.m.c.dof :: pred i a.c
//   forall i | 0 < i < b.m.c.dof :: pred i b.c
// Then, react and creates a joined postcondition
//   forall i | 0 < i < a.m.c.dof :: pred2 i a.c b.c

lemma LemmaShorOracleNoMod(dof : nat, c : array<(int, int)>, c' : array<(int, int)>,
  a : nat, N : nat, i : nat)
  requires N > 0
  requires Pow2(i) == dof
  requires c.Length >= dof >= 0
  requires forall k | 0 <= k < dof :: c[k] == (Pow(a, k) , 1)
  requires c'.Length >= 2 * dof >= 0
  requires forall k | 0 <= k < dof :: c'[k] == c[k]
  requires forall k | 0 <= k < dof :: c'[k + dof] == ((Pow(a, Pow2(i)) * c'[k].0), c'[k].1)
  ensures forall k | 0 <= k < 2 * dof :: c'[k] == (Pow(a, k) , 1)
{
  forall k | 0 <= k < dof {
    calc == {
     c'[k + dof] == ((Pow(a, dof) * c'[k].0), 1);
     c'[k + dof] == ((Pow(a, dof) * Pow(a, k)), 1);
     c'[k + dof].0 == (Pow(a, dof) * Pow(a, k));
     { LemmaPowAdds(a, dof, k); }
     c'[k + dof].0 == (Pow(a, dof + k));
     c'[k + dof] == (Pow(a, dof + k), 1);
    }
  }
  assert forall k | 0 <= k < dof :: c'[k + dof] == (Pow(a, dof + k), 1);
  assert forall k | dof <= k < 2 * dof :: 0 <= (k - dof) < dof;
}

lemma LemmaShorOracle(dof : nat, c' : array<(int, int)>, a : nat, N : nat, i : nat)
  requires N > 0
  requires 0 <= 2 * dof == c'.Length
  requires forall k | 0 <= k < dof :: c'[k] == (Pow(a, k) % N , 1)
  requires forall k | 0 <= k < dof :: c'[k + dof] == ((Pow(a, Pow2(i)) * c'[k].0) % N, c'[k].1)
  requires Pow2(i) == dof
  ensures forall k | 0 <= k < 2 * dof :: c'[k] == (Pow(a, k) % N, 1)
{
  forall k | 0 <= k < dof {
    calc == {
     c'[k + dof] == ((Pow(a, dof) * c'[k].0) % N, 1);
     c'[k + dof] == ((Pow(a, dof) * (Pow(a, k) % N)) % N, 1);
     { LemmaMulModNoopRightAuto(); }
     c'[k + dof] == ((Pow(a, dof) * Pow(a, k)) % N, 1);
     c'[k + dof].0 == (Pow(a, dof) * Pow(a, k) % N);
     { LemmaPowAdds(a, dof, k); }
     c'[k + dof].0 == (Pow(a, dof + k) % N);
     c'[k + dof] == (Pow(a, dof + k) % N, 1);
    }
  }
  assert forall k | 0 <= k < dof :: c'[k + dof] == (Pow(a, dof + k) % N, 1);
  assert forall k | dof <= k < 2 * dof :: 0 <= (k - dof) < dof;
}


method Shor1 (a : nat, N : nat, n : nat, yv : nat, x : Qubits, y : Qubits)
  returns ( xv : Qubits )
  requires N >= 2
  requires x != y
  requires x.m != y.m
  requires n == x.card == y.card > 0
  requires x.m.Nor?
  requires y.m.Nor?
  requires x.Wf() && y.Wf()
  requires (forall i | 0 <= i < n :: x.m.b[i] == 0)
  requires (forall i | 0 <= i < n :: y.m.b[i] == 0)
  ensures y.card == old(y.card)
  // ensures xv.m.CH? && y.m.CH? && xv.Wf() && y.Wf()
  // ensures forall k | 0 <= k < xv.m.dof :: xv.m.c[k] == (k, 1)
  // ensures y.m.dof == xv.m.dof == Pow2(y.card)
  // ensures forall k | 0 <= k < Pow2(y.card) :: y.m.c[k] == (Pow(a, k) % N, 1)
  modifies x, y, y.m.b
{
  ghost var tmp := y.m;
  y.Xat(0);
  LemmaB2NArrayTailingZeros(y.m.b, 0, 1);
  reveal b2nAux();
  assert b2nAux(y.m.b, 0, y.m.b.Length) == b2nAux(y.m.b, 0, 1) == y.m.b[0] == 1;
  assert (forall i | 1 <= i < n :: y.m.b[i] == 0);
  assert forall i | 0 <= i < n :: x.m.b[i] == 0;
  y.NorRetCH();

  assert y.m.c[0] == (1, 1);
  assert y.m.dof == 1;
  assert forall i | 0 <= i < n :: x.m.b[i] == 0;
  x.H();
  assert forall i | 0 <= i < x.card :: x.m.h[i] == 1;

  // TODO : discard [x] when performing compilation
  var len_x := x.card;

  // interesting one:
  // A QRegister that has 1 DOF but has no qubits in it
  // What's the mathematical meaning of this?
  var x' := new Qubits.EmptyCH();
  reveal Pow2();
  assert y.m.dof == 1;
  assert y.card == len_x;
  var i : nat := 0;
  LemmaSmallMod(1, N);
  assert forall k | 0 <= k < 1 :: y.m.c[k] == (Pow(a, k) % N, 1);
  while i < len_x
    invariant 0 <= i <= len_x
    invariant y.card == old(y.card) == len_x
    invariant x.m.Had? && x.Wf()
    invariant forall i | 0 <= i < x.m.h.Length :: x.m.h[i] == 1
    invariant i + x.card == len_x
    invariant x'.m.CH? && x'.Wf()
    invariant y.m.CH? && y.Wf()
    invariant x'.m.dof == Pow2(x'.card)
    invariant x'.m.dof == y.m.dof // interesting case
    invariant y.m.dof == Pow2(i)
    invariant forall k | 0 <= k < x'.m.dof :: x'.m.c[k] == (k, 1)
    invariant forall k | 0 <= k < Pow2(i) :: y.m.c[k] == (Pow(a, k) % N, 1)
    decreases len_x - i
  {
    ghost var x'dof := x'.m.dof;
    ghost var olddof := y.m.dof;
    var q := x.SplitPlus(1);
    assert 0 <= i <= y.card - 1;
    assert y.m.dof == Pow2(i) <= Pow2(y.card - 1) by {
      LemmaLePow2Covariant(i, y.card - 1);
      assert Pow2(i) <= Pow2(y.card - 1);
    }
    var oldy := ControlledOracle(q, y, i, a, N);
    assert forall k | 0 <= k < Pow2(i) :: y.m.c[k] == (Pow(a, k) % N, 1);
    LemmaShorOracle(Pow2(i), y.m.c, a, N, i);
    x'.CatPlusCH(q);
    assert forall k | 0 <= k < 2 * Pow2(i) :: y.m.c[k] == (Pow(a, k) % N, 1);
    assert forall k | 0 <= k < Pow2(i + 1) :: y.m.c[k] == (Pow(a, k) % N, 1);
    i := i + 1;
    assert forall k | 0 <= k < Pow2(i) :: y.m.c[k] == (Pow(a, k) % N, 1);
  }
  assert i >= len_x && 0 <= i <= len_x;
  // assert len_x - i == 0;
  // assert forall k | 0 <= k < Pow2(i) :: y.m.c[k] == (Pow(a, k) % N, 1);
  // assert forall k | 0 <= k < Pow2(len_x) :: y.m.c[k] == (Pow(a, k) % N, 1);
  xv := x';
  // assert y.m.dof == Pow2(y.card);
}


method Test()
{
  var n := 10;
  var x := new Qubits.Prepare0(n);
  var y := new Qubits.Prepare0(n);
  // var xv := Shor1(10, 7, n, 0, x, y);
}
