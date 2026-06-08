method {:testEntry} M()
{
  N();
  assert false;
}

method {:testEntry} N()
  ensures P();

predicate P()
{
  false
}

method {:test} Test0() {
M();
}

// REPEAT 1 - TIME: 3.7232993 s

method {:test} Test3() {
M();
}

// REPEAT 2 - TIME: 4.5898726 s

method {:test} Test4() {
M();
}

// REPEAT 3 - TIME: 5.4501221 s

method {:test} Test5() {
M();
}

// REPEAT 4 - TIME: 6.2951446 s

method {:test} Test6() {
M();
}

// REPEAT 5 - TIME: 7.1009607 s

method {:test} Test7() {
M();
}

// REPEAT 6 - TIME: 7.9894942 s

method {:test} Test8() {
M();
}

// REPEAT 7 - TIME: 8.774082 s

method {:test} Test9() {
M();
}

// REPEAT 8 - TIME: 9.5433528 s

method {:test} Test10() {
M();
}

// REPEAT 9 - TIME: 10.3479465 s

method {:test} Test11() {
M();
}

// REPEAT 10 - TIME: 11.3057383 s
