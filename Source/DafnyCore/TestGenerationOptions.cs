using System;
using System.Collections.Generic;
using JetBrains.Annotations;
using Bpl = Microsoft.Boogie;

namespace Microsoft.Dafny {

  public class TestGenerationOptions {
    public const string TestInlineAttribute = "testInline";
    public const string TestEntryAttribute = "testEntry";
    public bool WarnDeadCode = false;

    public bool IgnoreWarnings = false;
    public bool PassingFailing = false;
    public enum Modes { None, Block, InlinedBlock, Path, Spec };
    public Modes Mode = Modes.None;
    public uint SeqLengthLimit = 0;
    public uint TestCount = 1;
    [CanBeNull] public string PrintBpl = null;
    public bool ForcePrune = false;
    public string CoverageReport = null;
    public const uint DefaultTimeLimit = 20;

    public HashSet<String> FailedVerification = [];
  }
}
