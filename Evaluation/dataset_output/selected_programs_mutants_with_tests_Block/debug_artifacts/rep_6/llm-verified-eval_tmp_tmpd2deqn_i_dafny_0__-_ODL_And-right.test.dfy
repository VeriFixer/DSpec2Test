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
      if i != j {
        assert abs(numbers[i] - numbers[j]) < threshold;
        result := true;
        return;
      }
    }
  }
}

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
