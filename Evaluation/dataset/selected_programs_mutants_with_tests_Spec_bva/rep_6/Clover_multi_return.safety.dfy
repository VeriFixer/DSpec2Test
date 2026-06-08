method {:testEntry} MultipleReturns(x: int, y: int) returns (more: int, less: int)
  ensures more == x+y
  ensures less == x-y
{
  more := x + y;
  less := x - y;
}

method {:test} Test17() {
var r0, r1 := MultipleReturns(105, 105);
expect r0 == 105 + 105;
expect r1 == 105 - 105;
}

// REPEAT 6 - TIME: 10.897304 s
