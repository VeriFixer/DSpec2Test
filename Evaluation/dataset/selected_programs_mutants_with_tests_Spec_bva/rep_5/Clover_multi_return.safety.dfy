method {:testEntry} MultipleReturns(x: int, y: int) returns (more: int, less: int)
  ensures more == x+y
  ensures less == x-y
{
  more := x + y;
  less := x - y;
}

method {:test} Test16() {
var r0, r1 := MultipleReturns(104, 104);
expect r0 == 104 + 104;
expect r1 == 104 - 104;
}

// REPEAT 5 - TIME: 9.7724422 s
