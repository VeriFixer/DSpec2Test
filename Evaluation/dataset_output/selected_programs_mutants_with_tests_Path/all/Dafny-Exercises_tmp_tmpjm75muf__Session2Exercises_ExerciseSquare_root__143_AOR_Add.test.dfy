// Dafny-Exercises_tmp_tmpjm75muf__Session2Exercises_ExerciseSquare_root.dfy

method {:testEntry} mroot1(n: int) returns (r: int)
  requires n >= 0
  ensures r >= 0 && r * r <= n < (r + 1) * (r + 1)
{
  r := 0;
  while r + 1 + (r + 1) <= n
    invariant r >= 0 && r * r <= n
    decreases n - r * r
  {
    r := r + 1;
  }
}

method {:testEntry} mroot2(n: int) returns (r: int)
  requires n >= 0
  ensures r >= 0 && r * r <= n < (r + 1) * (r + 1)
{
  r := n;
  while n < r * r
    invariant 0 <= r <= n && n < (r + 1) * (r + 1)
    invariant r * r <= n ==> n < (r + 1) * (r + 1)
    decreases r
  {
    r := r - 1;
  }
}

method {:testEntry} mroot3(n: int) returns (r: int)
  requires n >= 0
  ensures r >= 0 && r * r <= n < (r + 1) * (r + 1)
{
  var y: int;
  var h: int;
  r := 0;
  y := n + 1;
  while y != r + 1
    invariant r >= 0 && r * r <= n < y * y && y >= r + 1
    decreases y - r
  {
    h := (r + y) / 2;
    if h * h <= n {
      r := h;
    } else {
      y := h;
    }
  }
}


method {:testEntry} mroot1(n:int) returns (r:int) //Cost O(root n)
requires n>=0
ensures r>=0 && r*r <= n <(r+1)*(r+1)
{
    r:=0;
	while (r+1)*(r+1) <=n
	 invariant r>=0 && r*r <=n
	  decreases n-r*r
	 {
	   r:=r+1;
	 }


}


method {:testEntry} mroot2(n:int) returns (r:int) //Cost O(n)
requires n>=0
ensures r>=0 && r*r <= n <(r+1)*(r+1)
{
    r:=n;
	while n<r*r
	invariant 0<=r<=n && n<(r+1)*(r+1)//write the invariant
	invariant r*r<=n ==> n<(r+1)*(r+1)
	decreases r//write the bound
	{
		r:=r-1;
	}


}

method {:testEntry} mroot3(n:int) returns (r:int) //Cost O(log n)
requires n>=0
ensures r>=0 && r*r <= n <(r+1)*(r+1)
{   var y:int;
    var h:int;
    r:=0;
	y:=n+1;
	//Search in interval [0,n+1) 
	while (y!=r+1) //[r,y]
	  invariant r>=0 && r*r<=n<y*y && y>=r+1//	write the invariant 
	  decreases y-r//write the bound
	 {
	   h:=(r+y)/2;
	   if (h*h<=n)
	     {r:=h;}
	   else
	     {y:=h;} 
	 }


}

method {:test} Test0() {
expect 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot1(0);
expect r0 >= 0 && r0 * r0 <= 0 < (r0 + 1) * (r0 + 1);
}
method {:test} Test1() {
expect 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot2(0);
expect r0 >= 0 && r0 * r0 <= 0 < (r0 + 1) * (r0 + 1);
}
method {:test} Test2() {
expect 0 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot3(0);
expect r0 >= 0 && r0 * r0 <= 0 < (r0 + 1) * (r0 + 1);
}

// REPEAT 1 - TIME: 30.3314934 s

method {:test} Test3() {
expect 1 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot1(1);
expect r0 >= 0 && r0 * r0 <= 1 < (r0 + 1) * (r0 + 1);
}
method {:test} Test4() {
expect 1 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot2(1);
expect r0 >= 0 && r0 * r0 <= 1 < (r0 + 1) * (r0 + 1);
}
method {:test} Test5() {
expect 1 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot3(1);
expect r0 >= 0 && r0 * r0 <= 1 < (r0 + 1) * (r0 + 1);
}

// REPEAT 2 - TIME: 54.7071914 s

method {:test} Test6() {
expect 2 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot1(2);
expect r0 >= 0 && r0 * r0 <= 2 < (r0 + 1) * (r0 + 1);
}
method {:test} Test7() {
expect 4 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot2(4);
expect r0 >= 0 && r0 * r0 <= 4 < (r0 + 1) * (r0 + 1);
}
method {:test} Test8() {
expect 2 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot3(2);
expect r0 >= 0 && r0 * r0 <= 2 < (r0 + 1) * (r0 + 1);
}

// REPEAT 3 - TIME: 78.0352725 s

method {:test} Test9() {
expect 4 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot1(4);
expect r0 >= 0 && r0 * r0 <= 4 < (r0 + 1) * (r0 + 1);
}
method {:test} Test10() {
expect 5 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot2(5);
expect r0 >= 0 && r0 * r0 <= 5 < (r0 + 1) * (r0 + 1);
}
method {:test} Test11() {
expect 3 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot3(3);
expect r0 >= 0 && r0 * r0 <= 3 < (r0 + 1) * (r0 + 1);
}

// REPEAT 4 - TIME: 101.8004652 s

method {:test} Test12() {
expect 16 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot1(16);
expect r0 >= 0 && r0 * r0 <= 16 < (r0 + 1) * (r0 + 1);
}
method {:test} Test13() {
expect 9 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot2(9);
expect r0 >= 0 && r0 * r0 <= 9 < (r0 + 1) * (r0 + 1);
}
method {:test} Test14() {
expect 4 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot3(4);
expect r0 >= 0 && r0 * r0 <= 4 < (r0 + 1) * (r0 + 1);
}

// REPEAT 5 - TIME: 127.7940723 s

method {:test} Test15() {
expect 100 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot1(100);
expect r0 >= 0 && r0 * r0 <= 100 < (r0 + 1) * (r0 + 1);
}
method {:test} Test16() {
expect 25 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot2(25);
expect r0 >= 0 && r0 * r0 <= 25 < (r0 + 1) * (r0 + 1);
}
method {:test} Test17() {
expect 5 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot3(5);
expect r0 >= 0 && r0 * r0 <= 5 < (r0 + 1) * (r0 + 1);
}

// REPEAT 6 - TIME: 156.6927531 s

method {:test} Test18() {
expect 169 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot1(169);
expect r0 >= 0 && r0 * r0 <= 169 < (r0 + 1) * (r0 + 1);
}
method {:test} Test19() {
expect 64 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot2(64);
expect r0 >= 0 && r0 * r0 <= 64 < (r0 + 1) * (r0 + 1);
}
method {:test} Test20() {
expect 6 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot3(6);
expect r0 >= 0 && r0 * r0 <= 6 < (r0 + 1) * (r0 + 1);
}

// REPEAT 7 - TIME: 187.6144103 s

method {:test} Test21() {
expect 170 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot1(170);
expect r0 >= 0 && r0 * r0 <= 170 < (r0 + 1) * (r0 + 1);
}
method {:test} Test22() {
expect 65 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot2(65);
expect r0 >= 0 && r0 * r0 <= 65 < (r0 + 1) * (r0 + 1);
}
method {:test} Test23() {
expect 7 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot3(7);
expect r0 >= 0 && r0 * r0 <= 7 < (r0 + 1) * (r0 + 1);
}

// REPEAT 8 - TIME: 214.3396686 s

method {:test} Test24() {
expect 171 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot1(171);
expect r0 >= 0 && r0 * r0 <= 171 < (r0 + 1) * (r0 + 1);
}
method {:test} Test25() {
expect 66 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot2(66);
expect r0 >= 0 && r0 * r0 <= 66 < (r0 + 1) * (r0 + 1);
}
method {:test} Test26() {
expect 8 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot3(8);
expect r0 >= 0 && r0 * r0 <= 8 < (r0 + 1) * (r0 + 1);
}

// REPEAT 9 - TIME: 257.0503107 s

method {:test} Test27() {
expect 256 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot1(256);
expect r0 >= 0 && r0 * r0 <= 256 < (r0 + 1) * (r0 + 1);
}
method {:test} Test28() {
expect 67 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot2(67);
expect r0 >= 0 && r0 * r0 <= 67 < (r0 + 1) * (r0 + 1);
}
method {:test} Test29() {
expect 9 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot3(9);
expect r0 >= 0 && r0 * r0 <= 9 < (r0 + 1) * (r0 + 1);
}

// REPEAT 10 - TIME: 314.7673669 s
