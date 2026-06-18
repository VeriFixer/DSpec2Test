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
      if i != j <==> abs(numbers[i] - numbers[j]) < threshold {
        assert abs(numbers[i] - numbers[j]) < threshold;
        result := true;
        return;
      }
    }
  }
}

method {:test} Test8() {
var seqreal0 : seq<real> := [2112.0, 4135.0, 1102.0, -(213.0 / 2.0), 2331.0, 9263.0, 6926.0, 1650.0];
var r0 := has_close_elements(seqreal0, 31545.0/2.0);
expect r0 <==> exists i, j :: 0 <= i < |seqreal0| && 0 <= j < |seqreal0| && i != j && abs(seqreal0[i] - seqreal0[j]) < 31545.0/2.0;
expect r0 ==> |seqreal0| > 1;
}
method {:test} Test9() {
var seqreal0 : seq<real> := [-(74142321440551800878713251850257.0 / 3906250000000000000000000000.0), 42445992621498379244249133467.0 / 1953125000000000000000000.0, 8221.0, -(52168925356381991101589081861221.0 / 9765625000000000000000000000.0), -(718220321630506779039235757643727.0 / 19531250000000000000000000000.0), -(1013287629808254553684905256036169.0 / 19531250000000000000000000000.0)];
var r0 := has_close_elements(seqreal0, 131420372838873887322834749196221.0/9765625000000000000000000000.0);
expect r0 <==> exists i, j :: 0 <= i < |seqreal0| && 0 <= j < |seqreal0| && i != j && abs(seqreal0[i] - seqreal0[j]) < 131420372838873887322834749196221.0/9765625000000000000000000000.0;
expect r0 ==> |seqreal0| > 1;
}

// REPEAT 5 - TIME: 8.7428705 s
