// Clover_compare.dfy

method {:testEntry} Compare<T(==)>(a: T, b: T) returns (eq: bool)
  ensures a == b ==> eq == true
  ensures a != b ==> eq == false
{
  if a == b {
    eq := true;
  } else {
  }
}

method {:test} Test6() {
var r0 := Compare<int>(0, 0);
expect 0 == 0 ==> r0 == true;
expect 0 != 0 ==> r0 == false;
}

// REPEAT 4 - TIME: 4.710964 s
