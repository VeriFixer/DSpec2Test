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

// REPEAT 1 - TIME: 2.8012674 s

method {:test} Test1() {
M();
}

// REPEAT 2 - TIME: 3.8315684 s

method {:test} Test2() {
M();
}

// REPEAT 3 - TIME: 4.7094954 s

method {:test} Test3() {
M();
}

// REPEAT 4 - TIME: 5.6958984 s

method {:test} Test4() {
M();
}

// REPEAT 5 - TIME: 6.6140584 s

method {:test} Test5() {
M();
}

// REPEAT 6 - TIME: 7.5286953 s

method {:test} Test6() {
M();
}

// REPEAT 7 - TIME: 8.233183 s

method {:test} Test7() {
M();
}

// REPEAT 8 - TIME: 8.8895535 s

method {:test} Test8() {
M();
}

// REPEAT 9 - TIME: 9.5269697 s

method {:test} Test9() {
M();
}

// REPEAT 10 - TIME: 10.2653748 s
