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

method {:test} Test9() {
var r0 := ContainsZ("\U{0004}a\U{0002}\0");
expect r0 <==> exists i :: 0 <= i < |"\U{0004}a\U{0002}\0"| && ("\U{0004}a\U{0002}\0"[i] == 'z' || "\U{0004}a\U{0002}\0"[i] == 'Z');
}
method {:test} Test10() {
var r0 := ContainsZ("\U{0005}\U{0001}Z\U{0003}");
expect r0 <==> exists i :: 0 <= i < |"\U{0005}\U{0001}Z\U{0003}"| && ("\U{0005}\U{0001}Z\U{0003}"[i] == 'z' || "\U{0005}\U{0001}Z\U{0003}"[i] == 'Z');
}
method {:test} Test11() {
var r0 := ContainsZ("aaaaaaa\U{0001}aa\U{0003}a\U{0007}aZ\taa\U{0005}aaa\U{000B}a");
expect r0 <==> exists i :: 0 <= i < |"aaaaaaa\U{0001}aa\U{0003}a\U{0007}aZ\taa\U{0005}aaa\U{000B}a"| && ("aaaaaaa\U{0001}aa\U{0003}a\U{0007}aZ\taa\U{0005}aaa\U{000B}a"[i] == 'z' || "aaaaaaa\U{0001}aa\U{0003}a\U{0007}aZ\taa\U{0005}aaa\U{000B}a"[i] == 'Z');
}

// REPEAT 4 - TIME: 219.4035754 s
