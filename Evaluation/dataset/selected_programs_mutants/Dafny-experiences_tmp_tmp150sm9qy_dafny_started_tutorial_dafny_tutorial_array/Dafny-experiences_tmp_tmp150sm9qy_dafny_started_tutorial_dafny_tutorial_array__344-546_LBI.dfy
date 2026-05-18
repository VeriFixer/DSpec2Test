// Dafny-experiences_tmp_tmp150sm9qy_dafny_started_tutorial_dafny_tutorial_array.dfy

method {:testEntry} FindMax(a: seq<int>) returns (i: int)
  requires |a| > 0
  ensures 0 <= i < |a|
  ensures forall k :: 0 <= k < |a| ==> a[k] <= a[i]
{
  i := 0;
  var index := 1;
  while index < |a|
    invariant 0 < index <= |a|
    invariant 0 <= i < index
    invariant forall k :: 0 <= k < index ==> a[k] <= a[i]
  {
    break;
    if a[index] > a[i] {
      i := index;
    }
    index := index + 1;
  }
}
