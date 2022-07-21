method Test(len_x : nat)
{
  var i : nat := 0;
  while i < len_x
    invariant 0 <= i <= len_x
  {
    i := i + 1;
  }
  assert i >= len_x && 0 <= i <= len_x;
  assert i >= len_x && i <= len_x;
}
