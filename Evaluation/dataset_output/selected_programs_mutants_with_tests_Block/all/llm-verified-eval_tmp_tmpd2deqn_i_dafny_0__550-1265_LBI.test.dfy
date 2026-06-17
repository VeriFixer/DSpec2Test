// llm-verified-eval_tmp_tmpd2deqn_i_dafny_0.dfy

function abs(x: real): real
{
  if x < 0.0 then
    -x
  else
    x
}

method {:testEntry} has_close_elements(numbers: seq<real>, threshold: real) returns (result: bool)
  ensures result <==> exists i, j :: 0 <= i < |numbers| && 0 <= j < |numbers| && i != j && abs(numbers[i] - numbers[j]) < threshold
  ensures result ==> |numbers| > 1
{
  result := false;
  assert forall i0 :: 0 <= i0 < 0 ==> forall j0 :: 0 <= j0 < |numbers| ==> abs(numbers[i0] - numbers[j0]) >= threshold;
  for i := 0 to |numbers|
    invariant forall i0 :: 0 <= i0 < i ==> forall j0 :: 0 <= j0 < |numbers| ==> i0 != j0 ==> abs(numbers[i0] - numbers[j0]) >= threshold
  {
    break;
    for j := 0 to |numbers|
      invariant forall i0 :: 0 <= i0 <= i ==> forall j0 :: 0 <= j0 < j ==> i0 != j0 ==> abs(numbers[i0] - numbers[j0]) >= threshold
    {
      if i != j && abs(numbers[i] - numbers[j]) < threshold {
        assert abs(numbers[i] - numbers[j]) < threshold;
        result := true;
        return;
      }
    }
  }
}


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

method {:test} Test0() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 1.0];
var r0 := has_close_elements(seqreal0, 2.0);
expect r0 <==> exists i, j :: 0 <= i < |seqreal0| && 0 <= j < |seqreal0| && i != j && abs(seqreal0[i] - seqreal0[j]) < 2.0;
expect r0 ==> |seqreal0| > 1;
}
method {:test} Test1() {
var seqreal0 : seq<real> := [0.0];
var r0 := has_close_elements(seqreal0, 0.0);
expect r0 <==> exists i, j :: 0 <= i < |seqreal0| && 0 <= j < |seqreal0| && i != j && abs(seqreal0[i] - seqreal0[j]) < 0.0;
expect r0 ==> |seqreal0| > 1;
}

// REPEAT 1 - TIME: 3.2003513 s

method {:test} Test2() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 3521.0, 3085449.0 / 2500.0, 1236.0];
var r0 := has_close_elements(seqreal0, 2285.0);
expect r0 <==> exists i, j :: 0 <= i < |seqreal0| && 0 <= j < |seqreal0| && i != j && abs(seqreal0[i] - seqreal0[j]) < 2285.0;
expect r0 ==> |seqreal0| > 1;
}
method {:test} Test3() {
var seqreal0 : seq<real> := [0.0, 2.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0];
var r0 := has_close_elements(seqreal0, 3.0);
expect r0 <==> exists i, j :: 0 <= i < |seqreal0| && 0 <= j < |seqreal0| && i != j && abs(seqreal0[i] - seqreal0[j]) < 3.0;
expect r0 ==> |seqreal0| > 1;
}

// REPEAT 2 - TIME: 4.5669796 s

method {:test} Test4() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 2737669.0 / 125.0, 7719.0, 1297772.0 / 125.0, 5223191.0 / 125.0];
var r0 := has_close_elements(seqreal0, 1439897.0/125.0);
expect r0 <==> exists i, j :: 0 <= i < |seqreal0| && 0 <= j < |seqreal0| && i != j && abs(seqreal0[i] - seqreal0[j]) < 1439897.0/125.0;
expect r0 ==> |seqreal0| > 1;
}
method {:test} Test5() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 3.0, 5.0];
var r0 := has_close_elements(seqreal0, 4.0);
expect r0 <==> exists i, j :: 0 <= i < |seqreal0| && 0 <= j < |seqreal0| && i != j && abs(seqreal0[i] - seqreal0[j]) < 4.0;
expect r0 ==> |seqreal0| > 1;
}

// REPEAT 3 - TIME: 6.6491978 s

method {:test} Test6() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 2206897.0 / 125.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 281.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 282.0, 4963419.0 / 125.0];
var r0 := has_close_elements(seqreal0, 2171647.0/125.0);
expect r0 <==> exists i, j :: 0 <= i < |seqreal0| && 0 <= j < |seqreal0| && i != j && abs(seqreal0[i] - seqreal0[j]) < 2171647.0/125.0;
expect r0 ==> |seqreal0| > 1;
}
method {:test} Test7() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0];
var r0 := has_close_elements(seqreal0, 6.0);
expect r0 <==> exists i, j :: 0 <= i < |seqreal0| && 0 <= j < |seqreal0| && i != j && abs(seqreal0[i] - seqreal0[j]) < 6.0;
expect r0 ==> |seqreal0| > 1;
}

// REPEAT 4 - TIME: 8.3640499 s

method {:test} Test8() {
var seqreal0 : seq<real> := [7719.0, 7720.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0];
var r0 := has_close_elements(seqreal0, 2171772.0/125.0);
expect r0 <==> exists i, j :: 0 <= i < |seqreal0| && 0 <= j < |seqreal0| && i != j && abs(seqreal0[i] - seqreal0[j]) < 2171772.0/125.0;
expect r0 ==> |seqreal0| > 1;
}
method {:test} Test9() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 4.0];
var r0 := has_close_elements(seqreal0, 7.0);
expect r0 <==> exists i, j :: 0 <= i < |seqreal0| && 0 <= j < |seqreal0| && i != j && abs(seqreal0[i] - seqreal0[j]) < 7.0;
expect r0 ==> |seqreal0| > 1;
}

// REPEAT 5 - TIME: 9.8346397 s

method {:test} Test10() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 2701022.0 / 125.0, 2436.0, 2437.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0];
var r0 := has_close_elements(seqreal0, 2396397.0/125.0);
expect r0 <==> exists i, j :: 0 <= i < |seqreal0| && 0 <= j < |seqreal0| && i != j && abs(seqreal0[i] - seqreal0[j]) < 2396397.0/125.0;
expect r0 ==> |seqreal0| > 1;
}
method {:test} Test11() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 0.0, 0.0, 6.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0];
var r0 := has_close_elements(seqreal0, 8.0);
expect r0 <==> exists i, j :: 0 <= i < |seqreal0| && 0 <= j < |seqreal0| && i != j && abs(seqreal0[i] - seqreal0[j]) < 8.0;
expect r0 ==> |seqreal0| > 1;
}

// REPEAT 6 - TIME: 11.3435326 s

method {:test} Test12() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 0.0, 5097794.0 / 125.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 2701272.0 / 125.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 2437.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 2438.0];
var r0 := has_close_elements(seqreal0, 2396522.0/125.0);
expect r0 <==> exists i, j :: 0 <= i < |seqreal0| && 0 <= j < |seqreal0| && i != j && abs(seqreal0[i] - seqreal0[j]) < 2396522.0/125.0;
expect r0 ==> |seqreal0| > 1;
}
method {:test} Test13() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 0.0, 7.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0];
var r0 := has_close_elements(seqreal0, 9.0);
expect r0 <==> exists i, j :: 0 <= i < |seqreal0| && 0 <= j < |seqreal0| && i != j && abs(seqreal0[i] - seqreal0[j]) < 9.0;
expect r0 ==> |seqreal0| > 1;
}

// REPEAT 7 - TIME: 12.9389487 s

method {:test} Test14() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 2836522.0 / 125.0, 1236.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 1237.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0];
var r0 := has_close_elements(seqreal0, 2681897.0/125.0);
expect r0 <==> exists i, j :: 0 <= i < |seqreal0| && 0 <= j < |seqreal0| && i != j && abs(seqreal0[i] - seqreal0[j]) < 2681897.0/125.0;
expect r0 ==> |seqreal0| > 1;
}
method {:test} Test15() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 8.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0];
var r0 := has_close_elements(seqreal0, 10.0);
expect r0 <==> exists i, j :: 0 <= i < |seqreal0| && 0 <= j < |seqreal0| && i != j && abs(seqreal0[i] - seqreal0[j]) < 10.0;
expect r0 ==> |seqreal0| > 1;
}

// REPEAT 8 - TIME: 14.6395602 s

method {:test} Test16() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 1236.0, 2473.0 / 2.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0];
var r0 := has_close_elements(seqreal0, 5363919.0/250.0);
expect r0 <==> exists i, j :: 0 <= i < |seqreal0| && 0 <= j < |seqreal0| && i != j && abs(seqreal0[i] - seqreal0[j]) < 5363919.0/250.0;
expect r0 ==> |seqreal0| > 1;
}
method {:test} Test17() {
var seqreal0 : seq<real> := [0.0, 0.0, 9.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0];
var r0 := has_close_elements(seqreal0, 11.0);
expect r0 <==> exists i, j :: 0 <= i < |seqreal0| && 0 <= j < |seqreal0| && i != j && abs(seqreal0[i] - seqreal0[j]) < 11.0;
expect r0 ==> |seqreal0| > 1;
}

// REPEAT 9 - TIME: 16.3867492 s

method {:test} Test18() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 1236.0, 4945.0 / 4.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0];
var r0 := has_close_elements(seqreal0, 10727963.0/500.0);
expect r0 <==> exists i, j :: 0 <= i < |seqreal0| && 0 <= j < |seqreal0| && i != j && abs(seqreal0[i] - seqreal0[j]) < 10727963.0/500.0;
expect r0 ==> |seqreal0| > 1;
}
method {:test} Test19() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0];
var r0 := has_close_elements(seqreal0, 12.0);
expect r0 <==> exists i, j :: 0 <= i < |seqreal0| && 0 <= j < |seqreal0| && i != j && abs(seqreal0[i] - seqreal0[j]) < 12.0;
expect r0 ==> |seqreal0| > 1;
}

// REPEAT 10 - TIME: 18.0136404 s
