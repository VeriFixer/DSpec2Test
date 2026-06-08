// dafny-synthesis_task_id_17.dfy

method {:testEntry} SquarePerimeter(side: int) returns (perimeter: int)
  requires side > 0
  ensures perimeter == 4 * side
{
  perimeter := 0;
}
