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

method {:test} Test17() {
var seqreal0 : seq<real> := [-(12837.0 / 2.0), 2437.0, 609.0];
var r0 := has_close_elements(seqreal0, 35425.0/2.0);
expect r0 <==> exists i, j :: 0 <= i < |seqreal0| && 0 <= j < |seqreal0| && i != j && abs(seqreal0[i] - seqreal0[j]) < 35425.0/2.0;
expect r0 ==> |seqreal0| > 1;
}
method {:test} Test18() {
var seqreal0 : seq<real> := [-(42405005232440086877374954911.0 / 625000000000000000000000.0), 2437.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, -(1042362630653740506808309.0 / 62500000000000000000.0), 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, -(18137461013812413471323711637.0 / 625000000000000000000000.0), -(27376117504703195784513711637.0 / 625000000000000000000000.0), -(17253718184285820665472166637.0 / 312500000000000000000000.0), -(4277487400827895546430621637.0 / 625000000000000000000000.0)];
var r0 := has_close_elements(seqreal0, 5707568863868445546430621637.0/625000000000000000000000.0);
expect r0 <==> exists i, j :: 0 <= i < |seqreal0| && 0 <= j < |seqreal0| && i != j && abs(seqreal0[i] - seqreal0[j]) < 5707568863868445546430621637.0/625000000000000000000000.0;
expect r0 ==> |seqreal0| > 1;
}

// REPEAT 2 - TIME: 10.3529232 s
