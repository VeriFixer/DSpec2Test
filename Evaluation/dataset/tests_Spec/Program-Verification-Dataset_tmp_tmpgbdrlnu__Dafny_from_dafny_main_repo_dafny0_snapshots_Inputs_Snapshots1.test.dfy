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

// REPEAT 1 - TIME: 2.5416021 s

method {:test} Test1() {
M();
}

// REPEAT 2 - TIME: 3.4162991 s

method {:test} Test2() {
M();
}

// REPEAT 3 - TIME: 4.3266442 s

method {:test} Test3() {
M();
}

// REPEAT 4 - TIME: 5.2026846 s

method {:test} Test4() {
M();
}

// REPEAT 5 - TIME: 6.1618377 s

method {:test} Test5() {
M();
}

// REPEAT 6 - TIME: 6.9485067 s

method {:test} Test6() {
M();
}

// REPEAT 7 - TIME: 7.6455527 s

method {:test} Test7() {
M();
}

// REPEAT 8 - TIME: 8.2766402 s

method {:test} Test8() {
M();
}

// REPEAT 9 - TIME: 8.8531777 s

method {:test} Test9() {
M();
}

// REPEAT 10 - TIME: 9.4552285 s
