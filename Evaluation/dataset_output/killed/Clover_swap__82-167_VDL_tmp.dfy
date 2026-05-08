// Clover_swap.dfy

method Swap(X: int, Y: int)
    returns (x: int, y: int)
  ensures x == Y
  ensures y == X
{
  x, y := X, Y;
  x := y;
  assert x == Y && y == X;
}
