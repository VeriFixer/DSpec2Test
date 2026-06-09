method {:testEntry} MultipleReturns(x: int, y: int) returns (more: int, less: int)
  ensures more == x+y
  ensures less == x-y
{
  more := x + y;
  less := x - y;
}

method {:test} Test4() {
var r0, r1 := MultipleReturns(4, 4);
expect r0 == 4 + 4;
expect r1 == 4 - 4;
}

// REPEAT 5 - TIME: 4.3404601 s
