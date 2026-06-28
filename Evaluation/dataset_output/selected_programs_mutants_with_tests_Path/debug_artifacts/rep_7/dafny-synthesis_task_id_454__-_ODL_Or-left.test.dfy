// dafny-synthesis_task_id_454.dfy

method {:testEntry} ContainsZ(s: string) returns (result: bool)
  ensures result <==> exists i :: 0 <= i < |s| && (s[i] == 'z' || s[i] == 'Z')
{
  result := false;
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant result <==> exists k :: 0 <= k < i && (s[k] == 'z' || s[k] == 'Z')
  {
    if s[i] == 'Z' {
      result := true;
      break;
    }
  }
}

method {:test} Test18() {
var r0 := ContainsZ("\U{0006}aaaaaaa\U{0002}\0\U{0004}a");
expect r0 <==> exists i :: 0 <= i < |"\U{0006}aaaaaaa\U{0002}\0\U{0004}a"| && ("\U{0006}aaaaaaa\U{0002}\0\U{0004}a"[i] == 'z' || "\U{0006}aaaaaaa\U{0002}\0\U{0004}a"[i] == 'Z');
}
method {:test} Test19() {
var r0 := ContainsZ("Za\U{0001}aaaaaa\U{0003}\U{0005}aaa\U{0007}aa\taa");
expect r0 <==> exists i :: 0 <= i < |"Za\U{0001}aaaaaa\U{0003}\U{0005}aaa\U{0007}aa\taa"| && ("Za\U{0001}aaaaaa\U{0003}\U{0005}aaa\U{0007}aa\taa"[i] == 'z' || "Za\U{0001}aaaaaa\U{0003}\U{0005}aaa\U{0007}aa\taa"[i] == 'Z');
}
method {:test} Test20() {
var r0 := ContainsZ("Zaaaaaaaa\U{0003}a\U{0007}aaaaa\t\U{0005}\U{0001}");
expect r0 <==> exists i :: 0 <= i < |"Zaaaaaaaa\U{0003}a\U{0007}aaaaa\t\U{0005}\U{0001}"| && ("Zaaaaaaaa\U{0003}a\U{0007}aaaaa\t\U{0005}\U{0001}"[i] == 'z' || "Zaaaaaaaa\U{0003}a\U{0007}aaaaa\t\U{0005}\U{0001}"[i] == 'Z');
}

// REPEAT 7 - TIME: 383.1099626 s
