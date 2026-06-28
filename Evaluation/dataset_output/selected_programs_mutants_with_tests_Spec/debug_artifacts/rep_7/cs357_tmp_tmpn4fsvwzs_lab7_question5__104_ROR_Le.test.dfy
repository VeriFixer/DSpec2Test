// cs357_tmp_tmpn4fsvwzs_lab7_question5.dfy

method {:testEntry} M1(x: int, y: int) returns (r: int)
  ensures r == x * y
  decreases x < 0, x
{
  if x <= 0 {
    r := 0;
  } else if x < 0 {
    r := M1(-x, y);
    r := -r;
  } else {
    r := M1(x - 1, y);
    r := A1(r, y);
  }
}

method {:testEntry} A1(x: int, y: int) returns (r: int)
  ensures r == x + y
{
  r := x;
  if y < 0 {
    var n := y;
    while n != 0
      invariant r == x + y - n
      invariant -n >= 0
    {
      r := r - 1;
      n := n + 1;
    }
  } else {
    var n := y;
    while n != 0
      invariant r == x + y - n
      invariant n >= 0
    {
      r := r + 1;
      n := n - 1;
    }
  }
}

method {:test} Test12() {
var r0 := M1(7725, 7725);
expect r0 == 7725 * 7725;
}
method {:test} Test13() {
var r0 := A1(6, 6);
expect r0 == 6 + 6;
}

// REPEAT 7 - TIME: 10.810067 s
