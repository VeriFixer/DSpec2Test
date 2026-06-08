method {:testEntry} MultipleReturns(x: int, y: int) returns (more: int, less: int)
  ensures more == x+y
  ensures less == x-y
{
  more := x + y;
  less := x - y;
}

method {:test} Test13() {
var r0, r1 := MultipleReturns(101, 101);
expect r0 == 101 + 101;
expect r1 == 101 - 101;
}

// REPEAT 2 - TIME: 8.1431875 s
