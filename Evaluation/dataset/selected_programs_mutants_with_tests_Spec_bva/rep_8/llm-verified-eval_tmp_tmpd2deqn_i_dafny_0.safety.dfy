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

method {:test} Test29() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 8855.0, 65680983.0 / 4000.0];
var r0 := has_close_elements(seqreal0, 92533.0/2.0);
expect r0 <==> exists i, j :: 0 <= i < |seqreal0| && 0 <= j < |seqreal0| && i != j && abs(seqreal0[i] - seqreal0[j]) < 92533.0/2.0;
expect r0 ==> |seqreal0| > 1;
}
method {:test} Test30() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0];
var r0 := has_close_elements(seqreal0, 3.0);
expect r0 <==> exists i, j :: 0 <= i < |seqreal0| && 0 <= j < |seqreal0| && i != j && abs(seqreal0[i] - seqreal0[j]) < 3.0;
expect r0 ==> |seqreal0| > 1;
}

// REPEAT 8 - TIME: 17.284684 s
