method {:testEntry} MultipleReturns(x: int, y: int) returns (more: int, less: int)
  ensures more == x+y
  ensures less == x-y
{
  more := x + y;
  less := x - y;
}

method {:test} Test20() {
var r0, r1 := MultipleReturns(108, 108);
expect r0 == 108 + 108;
expect r1 == 108 - 108;
}

// REPEAT 9 - TIME: 12.8105569 s
