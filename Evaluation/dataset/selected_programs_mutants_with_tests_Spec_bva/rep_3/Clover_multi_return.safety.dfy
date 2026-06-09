method {:testEntry} MultipleReturns(x: int, y: int) returns (more: int, less: int)
  ensures more == x+y
  ensures less == x-y
{
  more := x + y;
  less := x - y;
}

method {:test} Test14() {
var r0, r1 := MultipleReturns(102, 102);
expect r0 == 102 + 102;
expect r1 == 102 - 102;
}

// REPEAT 3 - TIME: 8.3796785 s
