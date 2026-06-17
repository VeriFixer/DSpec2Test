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

// REPEAT 1 - TIME: 2.7719973 s
