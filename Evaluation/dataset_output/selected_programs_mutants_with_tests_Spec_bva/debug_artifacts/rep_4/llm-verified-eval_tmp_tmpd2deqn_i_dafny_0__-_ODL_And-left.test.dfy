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
    for j := 0 to |numbers|
      invariant forall i0 :: 0 <= i0 <= i ==> forall j0 :: 0 <= j0 < j ==> i0 != j0 ==> abs(numbers[i0] - numbers[j0]) >= threshold
    {
      if abs(numbers[i] - numbers[j]) < threshold {
        assert abs(numbers[i] - numbers[j]) < threshold;
        result := true;
        return;
      }
    }
  }
}

method {:test} Test21() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 7065.0, -(14523.0 / 2.0), 1594.0, 582.0, 2211.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 7578.0, 1108.0];
var r0 := has_close_elements(seqreal0, 26569.0);
expect r0 <==> exists i, j :: 0 <= i < |seqreal0| && 0 <= j < |seqreal0| && i != j && abs(seqreal0[i] - seqreal0[j]) < 26569.0;
expect r0 ==> |seqreal0| > 1;
}
method {:test} Test22() {
var seqreal0 : seq<real> := [47568844657724087.0 / 312500000000.0, 0.0, 0.0, 116543109416763511.0 / 1250000000000.0, 36915932305587837.0 / 312500000000.0, 49875619805587837.0 / 1250000000000.0, 41531244805587837.0 / 625000000000.0, 6906.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0];
var r0 := has_close_elements(seqreal0, 31120619805587837.0/1250000000000.0);
expect r0 <==> exists i, j :: 0 <= i < |seqreal0| && 0 <= j < |seqreal0| && i != j && abs(seqreal0[i] - seqreal0[j]) < 31120619805587837.0/1250000000000.0;
expect r0 ==> |seqreal0| > 1;
}

// REPEAT 4 - TIME: 17.660888 s
