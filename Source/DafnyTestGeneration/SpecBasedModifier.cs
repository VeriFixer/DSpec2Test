// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

#nullable disable
using System.Collections.Generic;
using System.Linq;
using Microsoft.Boogie;
using Microsoft.Dafny;
using IdentifierExpr = Microsoft.Boogie.IdentifierExpr;
using LiteralExpr = Microsoft.Boogie.LiteralExpr;
using Program = Microsoft.Boogie.Program;
using Substituter = Microsoft.Boogie.Substituter;
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
    
      var procedure = implementation.Proc;
      var substMap = new Dictionary<Variable, Expr>();
      
      for (int i = 0; i < procedure.InParams.Count; i++) {
        substMap[procedure.InParams[i]] = new IdentifierExpr(Token.NoToken, implementation.InParams[i]);
      }
      
      for (int i = 0; i < procedure.OutParams.Count; i++) {
        substMap[procedure.OutParams[i]] = new IdentifierExpr(Token.NoToken, implementation.OutParams[i]);
      }

      var subst = Substituter.SubstitutionFromDictionary(substMap);
      
      string baseMethodName = implementation.VerboseName.Split(" ")[0];
      
      var reqClauses = procedure.Requires
        .Where(r => IsUserSpec(r.Condition))
        .Select(r => Substituter.Apply(subst, r.Condition))
        .ToList();
      
      var ensClauses = procedure.Ensures
        .Where(e => IsUserSpec(e.Condition))
        .Select(e => Substituter.Apply(subst, e.Condition))
        .ToList();
      
      var reqDnfCombs = DnfEngine.CalculateCombinations(reqClauses);
      var ensDnfCombs = DnfEngine.CalculateCombinations(ensClauses);
      
      int specTestIndex = 0;
      
      foreach (var preComb in reqDnfCombs) {
        foreach (var postComb in ensDnfCombs) {

          var fullComb = new List<Expr>(preComb);
          fullComb.AddRange(postComb);

          if (DnfEngine.FindContradiction(fullComb)) { continue; }
          
          string uniqueStateId = $"SpecComb_{baseMethodName}_{specTestIndex}";
          var captureStateAttr = new QKeyValue(new Token(), $"captureState_{baseMethodName}_{specTestIndex}", new List<object> { uniqueStateId });
          var captureAssumeCmd = new AssumeCmd(new Token(), new LiteralExpr(new Token(), true), captureStateAttr);
          entryBlock.Cmds.Add(captureAssumeCmd);
          
          var andExpr = DnfEngine.ConjoinExprs(fullComb);
          entryBlock.Cmds.Add(new AssumeCmd(new Token(), andExpr));
          entryBlock.Cmds.Add( new AssertCmd(new Token(), new LiteralExpr(new Token(), false)));

          var targetStates = Utils.AllBlockIds(entryBlock, DafnyInfo.Options)
            .Where(id => id != null && id.Contains(uniqueStateId))
            .ToHashSet();
          
          var record = modifications.GetProgramModification(program, implementation,
            targetStates,
            testEntryNames, $"{baseMethodName}_{specTestIndex++} (spec)");
          
          yield return record;
          
          var index = entryBlock.Cmds.FindIndex(cmd => cmd is AssumeCmd assumeCmd && assumeCmd.Attributes! is QKeyValue keyValue && keyValue.Key.Equals(captureStateAttr.Key));
          if (index != -1) {
            entryBlock.Cmds.RemoveRange(index, 3);
          }
        }
      }
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
    
    private bool IsUserSpec(Expr expr) {
      string str = expr.ToString();
    
      if (str.Contains("$Heap") || str.Contains("$Tick") || str.Contains("alloc")) {
        return false;
      }
    
      if (expr is LiteralExpr lit && lit.Val is bool b && b) {
        return false;
      }
    
      return true;
    }
  }
}