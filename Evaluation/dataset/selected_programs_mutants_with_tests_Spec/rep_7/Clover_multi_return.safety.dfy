method {:testEntry} MultipleReturns(x: int, y: int) returns (more: int, less: int)
  ensures more == x+y
  ensures less == x-y
{
  more := x + y;
  less := x - y;
}

method {:test} Test6() {
var r0, r1 := MultipleReturns(6, 6);
expect r0 == 6 + 6;
expect r1 == 6 - 6;
}

// REPEAT 7 - TIME: 8.2898934 s
