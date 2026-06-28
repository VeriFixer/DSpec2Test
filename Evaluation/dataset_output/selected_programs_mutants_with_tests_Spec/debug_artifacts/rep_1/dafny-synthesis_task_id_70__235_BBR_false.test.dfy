// dafny-synthesis_task_id_70.dfy

method {:testEntry} AllSequencesEqualLength(sequences: seq<seq<int>>) returns (result: bool)
  ensures result <==> forall i, j :: 0 <= i < |sequences| && 0 <= j < |sequences| ==> |sequences[i]| == |sequences[j]|
{
  if false {
    return true;
  }
  var firstLength := |sequences[0]|;
  result := true;
  for i := 1 to |sequences|
    invariant 1 <= i <= |sequences|
    invariant result <==> forall k :: 0 <= k < i ==> |sequences[k]| == firstLength
  {
    if |sequences[i]| != firstLength {
      result := false;
      break;
    }
  }
}

method {:test} Test0() {
var seqseqint0 : seq<seq<int>> := [];
var r0 := AllSequencesEqualLength(seqseqint0);
expect r0 <==> forall i, j :: 0 <= i < |seqseqint0| && 0 <= j < |seqseqint0| ==> |seqseqint0[i]| == |seqseqint0[j]|;
}
method {:test} Test1() {
var seqint0 : seq<int> := [];
var seqint1 : seq<int> := [];
var seqint2 : seq<int> := [];
var seqint3 : seq<int> := [];
var seqint4 : seq<int> := [];
var seqint5 : seq<int> := [];
var seqint6 : seq<int> := [];
var seqint7 : seq<int> := [];
var seqint8 : seq<int> := [];
var seqint9 : seq<int> := [];
var seqint10 : seq<int> := [];
var seqint11 : seq<int> := [];
var seqint12 : seq<int> := [];
var seqint13 : seq<int> := [];
var seqint14 : seq<int> := [];
var seqint15 : seq<int> := [];
var seqint16 : seq<int> := [];
var seqint17 : seq<int> := [];
var seqint18 : seq<int> := [];
var seqint19 : seq<int> := [];
var seqint20 : seq<int> := [0];
var seqseqint0 : seq<seq<int>> := [seqint0, seqint1, seqint2, seqint3, seqint4, seqint5, seqint6, seqint7, seqint8, seqint9, seqint10, seqint11, seqint12, seqint13, seqint14, seqint15, seqint16, seqint17, seqint18, seqint19, seqint20];
var r0 := AllSequencesEqualLength(seqseqint0);
expect r0 <==> forall i, j :: 0 <= i < |seqseqint0| && 0 <= j < |seqseqint0| ==> |seqseqint0[i]| == |seqseqint0[j]|;
}

// REPEAT 1 - TIME: 3.5959996 s
