function abs(x: real): real
{
  if x < 0.0 then -x else x
}

method {:testEntry} has_close_elements(numbers: seq<real>, threshold: real) returns (result: bool)
    ensures result <==> exists i, j ::
      0 <= i < |numbers| &&
      0 <= j < |numbers| &&
      i != j &&
      abs(numbers[i] - numbers[j]) < threshold
    ensures result ==> |numbers| > 1
{
    result := false;

    assert (forall i0 :: (0 <= i0 < 0 ==>
                   forall j0 :: (0 <= j0 < |numbers| ==>
                   abs(numbers[i0] - numbers[j0]) >= threshold)));

    for i := 0 to |numbers|
        invariant (forall i0 :: (0 <= i0 < i ==>
                   forall j0 :: (0 <= j0 < |numbers| ==>
                   (i0 != j0 ==>
                   abs(numbers[i0] - numbers[j0]) >= threshold))))
    {
        for j := 0 to |numbers|
             invariant (forall i0 :: (0 <= i0 <= i ==>
                        forall j0 :: (0 <= j0 < j ==>
                        (i0 != j0 ==>
                        abs(numbers[i0] - numbers[j0]) >= threshold))))
        {
            if i != j && abs(numbers[i] - numbers[j]) < threshold {
                assert abs(numbers[i] - numbers[j]) < threshold;
                result := true;
                return;
            }

        }
    }
}

method {:test} Test23() {
var seqreal0 : seq<real> := [5981.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 334.0, 0.0, 3960.0, 238968963.0 / 10000.0, 6019.0, 1391.0, 624.0, 7065.0];
var r0 := has_close_elements(seqreal0, 61061.0/2.0);
expect r0 <==> exists i, j :: 0 <= i < |seqreal0| && 0 <= j < |seqreal0| && i != j && abs(seqreal0[i] - seqreal0[j]) < 61061.0/2.0;
expect r0 ==> |seqreal0| > 1;
}
method {:test} Test24() {
var seqreal0 : seq<real> := [1323.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 77463.0 / 2.0, -(72171.0 / 2.0), -73494.0];
var r0 := has_close_elements(seqreal0, 74817.0/2.0);
expect r0 <==> exists i, j :: 0 <= i < |seqreal0| && 0 <= j < |seqreal0| && i != j && abs(seqreal0[i] - seqreal0[j]) < 74817.0/2.0;
expect r0 ==> |seqreal0| > 1;
}

// REPEAT 5 - TIME: 13.4868728 s
