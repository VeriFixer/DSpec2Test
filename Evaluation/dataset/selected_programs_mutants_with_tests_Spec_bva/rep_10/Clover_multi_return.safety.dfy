method {:testEntry} MultipleReturns(x: int, y: int) returns (more: int, less: int)
  ensures more == x+y
  ensures less == x-y
{
  more := x + y;
  less := x - y;
}

method {:test} Test21() {
var r0, r1 := MultipleReturns(109, 109);
expect r0 == 109 + 109;
expect r1 == 109 - 109;
}

// REPEAT 10 - TIME: 13.2729773 s
