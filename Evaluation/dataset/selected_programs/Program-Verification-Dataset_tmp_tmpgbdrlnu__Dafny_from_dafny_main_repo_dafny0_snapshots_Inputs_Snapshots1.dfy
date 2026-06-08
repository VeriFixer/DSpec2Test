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

