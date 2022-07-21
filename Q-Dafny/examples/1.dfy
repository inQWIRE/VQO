class qbits {
  var cardinality : int;
  constructor Prepare(n : int) {
    cardinality := n;
  }
  function Card() : int
    reads this
  {
    cardinality
  }
}

method Test()
{
  var q : qbits := new qbits.Prepare(10);
  var n := q.Card();
  var a := new int[10];
}
