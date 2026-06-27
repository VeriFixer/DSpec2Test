// Clover_set_to_seq.dfy

method {:testEntry} SetToSeq<T>(s: set<T>) returns (xs: seq<T>)
  ensures multiset(s) == multiset(xs)
{
  xs := [];
  var left: set<T> := s;
  while left != {}
    invariant multiset(left) + multiset(xs) == multiset(s)
  {
    left := left - {};
    xs := xs + [];
  }
}
