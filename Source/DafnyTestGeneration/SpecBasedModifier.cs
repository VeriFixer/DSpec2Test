// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

#nullable disable
using System.Collections.Generic;
using System.Linq;
using Microsoft.Boogie;
using Microsoft.Dafny;
using LiteralExpr = Microsoft.Boogie.LiteralExpr;
using Program = Microsoft.Boogie.Program;
using Token = Microsoft.Boogie.Token;

namespace DafnyTestGeneration {

  /// <summary>
  /// A version of ProgramModifier that inserts assertions into the code
  /// that fail for each requires statement from the specification
  /// </summary>
  public class SpecBasedModifier : ProgramModifier {
    private readonly Modifications modifications;
    private Implementation/*?*/ implementation; // the implementation currently traversed
    private Program/*?*/ program; // the original program

    public SpecBasedModifier(Modifications modifications) {
      this.modifications = modifications;
    }

    protected override IEnumerable<ProgramModification> GetModifications(Program p) {
      return VisitProgram(p);
    }

    private IEnumerable<ProgramModification> VisitImplementation(
      Implementation node) {
      implementation = node;
      if (!ImplementationIsToBeTested(node) ||
          !DafnyInfo.IsAccessible(node.VerboseName.Split(" ")[0])) {
        yield break;
      }
      var testEntryNames = Utils.DeclarationHasAttribute(implementation, TestGenerationOptions.TestInlineAttribute)
        ? TestEntries
        : [implementation.VerboseName];

      var entryBlock = node.Blocks.FirstOrDefault();
      if (entryBlock == null) {
        yield break;
      }

      var state = Utils.GetBlockId(entryBlock, DafnyInfo.Options);
      if (state == null) {
        yield break;
      }

      var assertCmd = new AssertCmd(new Token(), new LiteralExpr(new Token(), false));
      entryBlock.Cmds.Add(assertCmd);

      var record = modifications.GetProgramModification(program, implementation,
        Utils.AllBlockIds(entryBlock, DafnyInfo.Options).ToHashSet(),
        testEntryNames, $"{implementation.VerboseName.Split(" ")[0]} (spec)");

      if (!record.IsCovered(modifications)) {
        yield return record;
      }

      entryBlock.Cmds.RemoveAt(0);
    }

    private IEnumerable<ProgramModification> VisitProgram(Program node) {
      program = node;
      var implementations = node.Implementations.ToList();
      foreach (var implementation in implementations) {
        foreach (var modification in VisitImplementation(implementation)) {
          yield return modification;
        }
      }
    }
  }
}