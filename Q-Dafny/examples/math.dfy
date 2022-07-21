// RUN: %dafny /compile:0 /noNLarith "%s"
include "../libraries/src/NonlinearArithmetic/Power.dfy"

import opened Power

method Test()
{
  assert((1 % 2) == 1);
  var n := Pow(2, 10);
  Lemma1PowAuto();
  assert(n == 2);
}
