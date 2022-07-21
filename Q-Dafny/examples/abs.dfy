method Abs(x : int) returns (y : int)
  requires x > 0
  ensures 0 <= y
{
  return x;
}

// class Node {
//   ghost var List: seq<int>
//     ghost var Repr: set<Node>
//     var head: int
//     var next: Node? // Node? means a Node value or null

//     predicate Valid()
//       reads this, Repr
//     {
//       this in Repr &&
//         1 <= |List| && List[0] == head &&
//         (next == null ==> |List| == 1) &&
//         (next != null ==>
//         next in Repr && next.Repr <= Repr && this !in next.Repr &&
//         next.Valid() && next.List == List[1..])
//     }

//     static method Cons(x: int, tail: Node?) returns (n: Node)
//       requires tail == null || tail.Valid()
//       ensures n.Valid()
//       ensures (if tail == null then n.List == [x] else n.List == [x] + tail.List)
//     {
//       n := new Node;
//       n.head, n.next := x, tail;
//       if (tail == null) {
//         n.List := [x];
//         n.Repr := {n};
//       } else {
//         n.List := [x] + tail.List;
//         n.Repr := {n} + tail.Repr;
//       }
//     }
// }

// method Search(ll: Node?) returns (r: int)
//   requires ll == null || ll.Valid()
//   ensures ll == null ==> r == 0
//   ensures ll != null ==>
//   0 <= r && r <= |ll.List| &&
//   (r < |ll.List| ==> ll.List[r] == 0 &&
//   0 !in ll.List[..r]) &&
//   (r == |ll.List| ==> 0 !in ll.List)
// {
//   if (ll == null) {
//     r := 0;
//   } else {
//     var jj,i := ll,0;
//     while (jj != null && jj.head != 0)
//       invariant jj != null ==> jj.Valid() &&
//       i + |jj.List| == |ll.List| &&
//       ll.List[i..] == jj.List
//       invariant jj == null ==> i == |ll.List|
//       invariant 0 !in ll.List[..i]
//       decreases |ll.List| - i
//     {
//       jj := jj.next;
//       i := i + 1;
//     }
//     r := i;
//   }
// }

// method Main()
// {
//   var list: Node? := null;
//   list := list.Cons(0, list);
//   list := list.Cons(5, list);
//   list := list.Cons(0, list);
//   list := list.Cons(8, list);
//   var r := Search(list);
//   print "Search returns ", r, "\n";
//   assert r == 1;
// }
