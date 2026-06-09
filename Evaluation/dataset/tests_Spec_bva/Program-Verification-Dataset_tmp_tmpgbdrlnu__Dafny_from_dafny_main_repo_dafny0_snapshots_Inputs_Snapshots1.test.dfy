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

// REPEAT 1 - TIME: 2.8590381 s

method {:test} Test3() {
M();
}

// REPEAT 2 - TIME: 3.6814149 s

method {:test} Test4() {
M();
}

// REPEAT 3 - TIME: 4.6407029 s

method {:test} Test5() {
M();
}

// REPEAT 4 - TIME: 5.5185267 s

method {:test} Test6() {
M();
}

// REPEAT 5 - TIME: 6.4422472 s

method {:test} Test7() {
M();
}

// REPEAT 6 - TIME: 7.1885334 s

method {:test} Test8() {
M();
}

// REPEAT 7 - TIME: 8.0347563 s

method {:test} Test9() {
M();
}

// REPEAT 8 - TIME: 8.6999943 s

method {:test} Test10() {
M();
}

// REPEAT 9 - TIME: 9.3037231 s

method {:test} Test11() {
M();
}

// REPEAT 10 - TIME: 10.1107226 s
