include "../libraries/src/NonlinearArithmetic/Power.dfy"

// Exponential Number
module Exp {
  import opened Power
  // [E] shouldn't be useful, but keep it anyway
  const E : real := 2.71828;

  datatype ExpMode =
    | RoU(N : nat, idx : nat)   // Pow(E, 2 * Pi * i * idx / N)
    
  // Exponentiation number with `i` on the exponent
  class {:autocontracts} IExp {
    var value : ExpMode;

    constructor mkRoU(N : nat, idx : nat)
      requires N >= 1;
      ensures this.value.RoU?
      ensures this.value.N == N && this.value.idx == idx
    {
      this.value := RoU(N, idx);
    }
    
    predicate Valid()
    {
      match value {
        case RoU(N, _) => N >= 1
      }
    }

    function Norm() : nat
    {
      match value {
        case RoU(_, _) => 1 
      }
    }

    method Div(idx : nat)
      requires value.RoU?
      requires idx <= value.idx
      ensures value.idx == old(value.idx) - idx && value.N == old(value.N)
    {
      value := RoU(value.N, value.idx - idx);
    }

  }
}
