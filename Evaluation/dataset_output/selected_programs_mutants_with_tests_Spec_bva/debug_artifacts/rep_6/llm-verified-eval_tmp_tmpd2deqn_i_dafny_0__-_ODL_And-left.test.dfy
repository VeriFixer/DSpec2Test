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

method {:test} Test25() {
var seqreal0 : seq<real> := [0.0, 0.0, 0.0, 0.0, 0.0, 531.0, 4186.0, 13728823.0 / 500.0, 6019.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 3023.0, 8935.0, 1573.0];
var r0 := has_close_elements(seqreal0, 28367.0);
expect r0 <==> exists i, j :: 0 <= i < |seqreal0| && 0 <= j < |seqreal0| && i != j && abs(seqreal0[i] - seqreal0[j]) < 28367.0;
expect r0 ==> |seqreal0| > 1;
}
method {:test} Test26() {
var seqreal0 : seq<real> := [890830442427764911754943210527808443832669006702047.0 / 12207031250000000000000000000000000000000000000.0, 409343663952115246789276731143251084934715766331409.0 / 12207031250000000000000000000000000000000000000.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 1028715177718356806481664812730920076500393616077047.0 / 6103515625000000000000000000000000000000000000.0, 0.0, 0.0, 1673996024748616523181310651533602001077648862486141.0 / 12207031250000000000000000000000000000000000000.0, 644079107980665995709510578749720758806816099767047.0 / 6103515625000000000000000000000000000000000000.0, 867.0, 0.0, 0.0, 0.0, 0.0, 0.0];
var r0 := has_close_elements(seqreal0, 347698495879727459646438663956035483464016662952047.0/12207031250000000000000000000000000000000000000.0);
expect r0 <==> exists i, j :: 0 <= i < |seqreal0| && 0 <= j < |seqreal0| && i != j && abs(seqreal0[i] - seqreal0[j]) < 347698495879727459646438663956035483464016662952047.0/12207031250000000000000000000000000000000000000.0;
expect r0 ==> |seqreal0| > 1;
}

// REPEAT 6 - TIME: 15.7035706 s
