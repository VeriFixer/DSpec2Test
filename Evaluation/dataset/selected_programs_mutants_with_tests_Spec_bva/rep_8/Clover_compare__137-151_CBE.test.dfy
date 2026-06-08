// Clover_compare.dfy

method {:testEntry} Compare<T(==)>(a: T, b: T) returns (eq: bool)
  ensures a == b ==> eq == true
  ensures a != b ==> eq == false
{
  eq := true;
}

method {:test} Test22() {
var r0 := Compare<int>(0, 0);
expect 0 == 0 ==> r0 == true;
expect 0 != 0 ==> r0 == false;
}

// REPEAT 8 - TIME: 31.7168966 s
