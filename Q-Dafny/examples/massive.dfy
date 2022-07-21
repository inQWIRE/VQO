predicate sortedSeq(a : seq<int>)
{
  forall i, j :: (0 <= i < j < |a| ==> a[i] <= a[j])
}

method Max(a : int, b : int) returns (c : int)
  ensures c >= a && c >= b
  ensures c == a || c == b
{
  if (a > b) {
    return a;
  } else {
    return b;
  }
}

method TestMax() {
  var x := 1;
  var y := 2;
  var mx := Max(x, y);
  assert (mx == y);
  x, y := y, x;
  mx := Max(x, y);
  assert(mx == x);
}


method AbsN(x : int) returns (y : int)
  requires x < 0;
  ensures y == -x
{
  return -x;
}

method Abs2(x: int) returns (y: int)
  requires x == -1
  ensures 0 <= y
  ensures 0 <= x ==> y == x
  ensures x < 0 ==> y == -x
{
  y := x + 2;
}
method Abs1(x: int) returns (y: int)
  requires false
  ensures 0 <= y
  ensures 0 <= x ==> y == x
  ensures x < 0 ==> y == -x
{
  y := x + 1;
}


function max(a : int, b : int) : int
{
  if (a > b) then a else b
}

method Testing() {
  assert (max(1, 10) == 10);
  assert (max(10, 1) == 10);
  var c := max(2, 20);
}

method Maxf(a : int, b : int) returns (c : int)
  ensures c == max(a, b)
{
  if (a > b) {
    return a;
  } else {
    return b;
  }
}


function fib(n : nat) : nat
{
  if n == 0 then 0
  else if n == 1 then 1
  else fib(n - 1) + fib(n - 2)
}

method IterativeFib(n : nat) returns (b : nat)
  ensures b == fib(n)
{
  if n == 0 {
    return 0;
  }
  
  var i := 1;
  var a := 0;
  b := 1;
  while (i != n)
    invariant 0 < i <= n
    invariant a == fib(i - 1)
    invariant b == fib(i)
    decreases (n - i)
  {
    i := i + 1;
    b, a := a + b, b;
  }
}

method TestFib()
{
  var x := IterativeFib(0);
  assert (x == 0);
  x := IterativeFib(1);
  assert (x == 1);
  x := IterativeFib(2);
  assert (x == 1);
  x := IterativeFib(3);
  assert (x == 2);
  x := IterativeFib(4);
  assert (x == 3);
}


method m(n: nat)
{
  var i: int := 0;
  while i != n
    invariant 0 <= i <= n
  {
    i := i + 1;
  }
  assert i == n;
}

method ComputeFib(n: nat) returns (b: nat)
   ensures b == fib(n)
{
  var i: int := 0;
  b := 0;
  var c := 1;

  while (i < n)
    invariant 0 <= i <= n
    invariant b == fib(i)
    invariant c == fib(i + 1)
  {
    b, c := c, b + c;
    i := i + 1;
  }

  return b;
}

method Find(a: array<int>, key: int) returns (index: int)
   ensures 0 <= index ==> index < a.Length && a[index] == key
{
  index := 0; 
  while (index < a.Length) 
    decreases a.Length - index
  {
    if (a[index] == key) {
      return index;
    }

    index := index + 1;
  }

  return -1;
}

method FindRefine(a: array<int>, key: int) returns (index: int)
  ensures 0 <= index ==> index < a.Length && a[index] == key
  ensures index < 0 ==> forall k :: 0 <= k < a.Length ==> a[k] != key
{
  index := 0; 
  while (index < a.Length)
    invariant 0 <= index <= a.Length
    invariant forall i :: 0 <= i < index ==> a[i] != key
    decreases a.Length - index
  {
    if (a[index] == key) {
      return index;
    }
    index := index + 1;
  }

  return -1;
}

method FindMax(a: array<int>) returns (i: int)
  requires a.Length > 0
  ensures 0 <= i < a.Length
  ensures forall k :: 0 <= k < a.Length ==> a[k] <= a[i]
{
  var j := 1;
  i := 0;
  while (j < a.Length)
    invariant 0 <= i < j <= a.Length
    invariant forall k :: 0 <= k < j ==> a[k] <= a[i]
    decreases (a.Length - j)
  {
    if (a[i] <= a[j]) {
      i := j;
    }
    j := j + 1;
  }
}

predicate sorted(a : array<int>)
  reads a
{
  forall i, j :: 0 <= i < j < a.Length ==> a[i] < a[j]
}

method BinarySearch(a : array<int>, value : int) returns (index : int)
  requires sorted(a)
  requires a.Length > 0
  ensures 0 <= index ==> (index < a.Length) && (a[index] == value)
  ensures index < 0 ==> forall i :: 0 <= i < a.Length ==> a[i] != value
{
  var left := 0;
  var right := a.Length;

  while (left + 1 < right)
    decreases right - left
    invariant 0 <= left < right <= a.Length
    invariant forall i :: 0 <= i < left ==> a[i] < value
    invariant forall j :: right <= j < a.Length ==> a[j] > value
  {
    var mid := (right + left) / 2;
    if a[mid] == value
    {
      return mid;
    }
    else if a[mid] < value
    {
      left := mid;
    }
    else
    {
      right := mid;
    }
  }
  index := if a[left] == value then left else -1;
}


predicate isReversed

method Short()
{
  var a1 := new int[100];
  var b1 := new int[100];
  var i := 0;
  while (i < a1.Length)
    invariant 0 <= i <= a1.Length
    invariant (forall k | 0 <= k < i :: a1[k] == b1[k])
    decreases (a1.Length - i)
  {
    b1[i] := a1[i];
    i := i + 1;
  }

  i := 0;
  while (i < a1.Length)
    invariant 0 <= i <= a1.Length
    decreases (a1.Length - i)
    invariant (forall k | 0 <= k < i :: a1[k] == b1[a1.Length - 1 - k])
  {
    a1[i], a1[a1.Length - 1 - i] := b1[a1.Length - 1 - i], b1[i];
    i := i + 1;
  }

  assert (forall i :: 0 <= i < a1.Length ==> a1[i] == b1[a1.Length - 1 - i]);
}

method Massive()
{
  var a1 := new int[10000000];
  var b1 := new int[10000000];
  var i := 0;
  while (i < a1.Length)
    invariant 0 <= i <= a1.Length
    invariant (forall k | 0 <= k < i :: a1[k] == b1[k])
    decreases (a1.Length - i)
  {
    b1[i] := a1[i];
    i := i + 1;
  }

  i := 0;
  while (i < a1.Length)
    invariant 0 <= i <= a1.Length
    decreases (a1.Length - i)
    invariant (forall k | 0 <= k < i :: a1[k] == b1[a1.Length - 1 - k])
  {
    a1[i], a1[a1.Length - 1 - i] := b1[a1.Length - 1 - i], b1[i];
    i := i + 1;
  }

  assert (forall i :: 0 <= i < a1.Length ==> a1[i] == b1[a1.Length - 1 - i]);
}

