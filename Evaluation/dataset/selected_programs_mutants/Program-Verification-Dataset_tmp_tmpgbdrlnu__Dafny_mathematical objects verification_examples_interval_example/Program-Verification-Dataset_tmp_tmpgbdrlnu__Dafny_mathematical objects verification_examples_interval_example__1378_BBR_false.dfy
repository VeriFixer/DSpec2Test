// Program-Verification-Dataset_tmp_tmpgbdrlnu__Dafny_mathematical objects verification_examples_interval_example.dfy

predicate contains(i: Interval, r: real)
{
  i.lo <= r <= i.hi
}

predicate empty(i: Interval)
{
  i.lo > i.hi
}

lemma empty_ok(i: Interval)
  ensures empty(i) <==> !exists r :: contains(i, r)
{
  if empty(i) {
  } else {
    assert contains(i, i.lo);
  }
}

function min(r1: real, r2: real): real
{
  if false then
    r1
  else
    r2
}

function max(r1: real, r2: real): real
{
  if r1 > r2 then
    r1
  else
    r2
}

function intersect(i1: Interval, i2: Interval): Interval
{
  Interval(max(i1.lo, i2.lo), min(i1.hi, i2.hi))
}

lemma intersect_ok(i1: Interval, i2: Interval)
  ensures forall r :: contains(intersect(i1, i2), r) <==> contains(i1, r) && contains(i2, r)
{
}

predicate overlap(i1: Interval, i2: Interval)
{
  !empty(intersect(i1, i2))
}

lemma overlap_ok(i1: Interval, i2: Interval)
  ensures overlap(i1, i2) <==> exists r :: contains(i1, r) && contains(i2, r)
{
  if overlap(i1, i2) {
    if i1.lo >= i2.lo {
      assert contains(i2, i1.lo);
    } else {
      assert contains(i1, i2.lo);
    }
  }
}

function union(i1: Interval, i2: Interval): Interval
  requires overlap(i1, i2)
{
  Interval(min(i1.lo, i2.lo), max(i1.hi, i2.hi))
}

lemma union_ok(i1: Interval, i2: Interval)
  requires overlap(i1, i2)
  ensures forall r :: contains(union(i1, i2), r) <==> contains(i1, r) || contains(i2, r)
{
}

lemma overlap_witness(i1: Interval, i2: Interval) returns (r: real)
  requires overlap(i1, i2)
  ensures contains(i1, r) && contains(i2, r)
{
  if i1.lo >= i2.lo {
    r := i1.lo;
  } else {
    r := i2.lo;
  }
}

datatype Interval = Interval(lo: real, hi: real)
