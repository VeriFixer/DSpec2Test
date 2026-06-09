method {:testEntry} MultipleReturns(x: int, y: int) returns (more: int, less: int)
  ensures more == x+y
  ensures less == x-y
{
  more := x + y;
  less := x - y;
}

method {:test} Test15() {
var r0, r1 := MultipleReturns(103, 103);
expect r0 == 103 + 103;
expect r1 == 103 - 103;
}

// REPEAT 4 - TIME: 9.0865643 s
