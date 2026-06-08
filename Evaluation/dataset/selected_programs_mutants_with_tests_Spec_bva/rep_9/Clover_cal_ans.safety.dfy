method {:testEntry} CalDiv() returns (x:int, y:int)
  ensures x==191/7
  ensures y==191%7
{

  x, y := 0, 191;
  while 7 <= y
    invariant 0 <= y && 7 * x + y == 191
  {
    x := x+1;
    y:=191-7*x;
  }
}

method {:test} Test12() {
var r0, r1 := CalDiv();
expect r0 == 191 / 7;
expect r1 == 191 % 7;
}

// REPEAT 9 - TIME: 12.2498961 s
