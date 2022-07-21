method Test() {
  // var b : nor;
  var a : Nor := Nor(10, seq(10, _ => 0));
  assert a.Nor?;
  assert a.n == 10;
  assert a.b[9] == 0;
}

method A(a : nor, b : seq)
  requires forall i :: i in a ==> i == 10
{
  // assert a == b;
  assert 1 == 1;

  assert b![1] == 0;
}
