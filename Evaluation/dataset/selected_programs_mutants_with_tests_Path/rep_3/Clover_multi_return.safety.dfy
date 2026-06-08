method {:testEntry} MultipleReturns(x: int, y: int) returns (more: int, less: int)
  ensures more == x+y
  ensures less == x-y
{
  more := x + y;
  less := x - y;
}

method {:test} Test2() {
var r0, r1 := MultipleReturns(2, 2);
expect r0 == 2 + 2;
expect r1 == 2 - 2;
}

// REPEAT 3 - TIME: 5.0306885 s
