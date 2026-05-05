using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.CommandLine;
using System.IO;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using DafnyCore;
using DafnyTestGeneration;
using Microsoft.Boogie;
using DafnyDriver.Commands;
using System.Diagnostics;
using System.Reflection;
using System.Globalization;

// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

#nullable disable
namespace Microsoft.Dafny;

static class GenerateTestsCommand {
  public static IEnumerable<Option> Options {
    get {
      return new Option[] { 
        Fdnf, 
        Bva,
        Simplify,
        IgnoreWarnings,
        PassingFailing,
        LoopUnroll,
        SequenceLengthLimit,
        TestCount,
        BoogieOptionBag.SolverLog,
        BoogieOptionBag.SolverOption,
        BoogieOptionBag.SolverOptionHelp,
        BoogieOptionBag.SolverPath,
        BoogieOptionBag.SolverPlugin,
        BoogieOptionBag.SolverResourceLimit,
        BoogieOptionBag.VerificationTimeLimit,
        PrintBpl,
        ExpectedCoverageReport,
        CommonOptionBag.NoTimeStampForCoverageReport,
        ForcePrune,
      }.Concat(DafnyCommands.ConsoleOutputOptions.Except(new[] { CommonOptionBag.AllowWarnings }).ToList()).
        Concat(DafnyCommands.ResolverOptions);
    }
  }

  private enum Mode {
    Path,
    Block,
    InlinedBlock,
    Spec
  }

  private static readonly Argument<Mode> modeArgument = new("mode", @"
Block - Generate tests targeting block-coverage.
InlinedBlock - Generate tests targeting block coverage after inlining (call-graph sensitive block coverage).
Path - Generate tests targeting path-coverage.
Spec - Generate specification-based tests (i.e. assume the specification is correct).");

  public static Command Create() {
    var result = new Command("generate-tests", "(Experimental) Generate Dafny tests that ensure block or path coverage of a particular Dafny program.");
    result.AddArgument(modeArgument);
    result.AddArgument(DafnyCommands.FilesArgument);

    foreach (var option in Options) {
      result.AddOption(option);
    }
    
    result.AddValidator(commandResult => {
      var mode = commandResult.GetValueForArgument(modeArgument);
      var hasFdnf = commandResult.FindResultFor(Fdnf) is not null;
      var hasBva = commandResult.FindResultFor(Bva) is not null;
      var hasTestCount = commandResult.FindResultFor(TestCount) is not null;
      var hasSimplify = commandResult.FindResultFor(Simplify) is not null;
      
      if (mode != Mode.Spec) {
        var invalidFlags = new List<string>();
        if (hasFdnf) {
          invalidFlags.Add("--fdnf");
        }
        if (hasBva) {
          invalidFlags.Add("--bva");
        }
        if (hasSimplify) {
          invalidFlags.Add("--simplify");
        }

        if (invalidFlags.Count > 0) {
          commandResult.ErrorMessage =
            $"*** Error: The following options can only be used when the mode is 'Spec': {string.Join(", ", invalidFlags)}";
        }
      } else {
        if (hasBva && hasTestCount) {
          commandResult.ErrorMessage = "*** Error: --bva and --test-count cannot be used simultaneously";
        }
      }
    });
    
    CultureInfo.DefaultThreadCurrentCulture = CultureInfo.InvariantCulture;
    CultureInfo.DefaultThreadCurrentUICulture = CultureInfo.InvariantCulture;

    DafnyNewCli.SetHandlerUsingDafnyOptionsContinuation(result, async (options, context) => {
      var mode = context.ParseResult.GetValueForArgument(modeArgument) switch {
        Mode.Path => TestGenerationOptions.Modes.Path,
        Mode.Block => TestGenerationOptions.Modes.Block,
        Mode.InlinedBlock => TestGenerationOptions.Modes.InlinedBlock,
        Mode.Spec => TestGenerationOptions.Modes.Spec,
        _ => throw new ArgumentOutOfRangeException()
      };
      PostProcess(options, mode);

      var exitCode = await GenerateTests(options);
      return (int)exitCode;
    });

    return result;
  }

  public static async Task<ExitValue> GenerateTests(DafnyOptions options) {
    var (exitValue, dafnyFiles, _) = await SynchronousCliCompilation.GetDafnyFiles(options);
    if (exitValue != ExitValue.SUCCESS) {
      return exitValue;
    }

    if (dafnyFiles.Count > 1 &&
        options.TestGenOptions.Mode != TestGenerationOptions.Modes.None) {
      await options.OutputWriter.Status(
        "*** Error: Only one .dfy file can be specified for testing");
      return ExitValue.PREPROCESSING_ERROR;
    }

    options.TestGenOptions.FailedVerification = await GetUnverified(options);

    var dafnyFileNames = DafnyFile.FileNames(dafnyFiles);

    var uri = new Uri(dafnyFileNames[0]);
    var source = new StreamReader(dafnyFileNames[0]);
    var coverageReport = new CoverageReport(name: "Expected Test Coverage", units: "Lines", suffix: "_tests_expected", program: null);
    if (options.TestGenOptions.WarnDeadCode) {
      await foreach (var line in TestGenerator.GetDeadCodeStatistics(source, uri, options, coverageReport)) {
        await options.OutputWriter.Status(line);
      }
    } else {
      var header = new StringBuilder();
      var testMethods = new List<string>();

      await foreach (var line in TestGenerator.GetTestClassForProgram(source, uri, options, coverageReport)) {
        if (options.TestGenOptions.PassingFailing) {
          if (line.StartsWith("include")) {
            header.AppendLine(line + "\n");
          } else if (line.Trim().StartsWith("method")) {
            testMethods.Add(line);
          }
        } else {
          await options.OutputWriter.Status(line);
        }
      }

      if (options.TestGenOptions.PassingFailing && testMethods.Count > 0) {
        var passingTests = new ConcurrentBag<string>();
        var failingTests = new ConcurrentBag<string>();
        
        await Parallel.ForEachAsync(testMethods, async (method, _) => {
          bool success = await RunSingleTest(header.ToString(), method);
          if (success) {
            passingTests.Add(method);
          } else {
            failingTests.Add(method);
          }
        });

        foreach (var line in TestGenerator.GetPassingFailingTests(header, passingTests.ToList(), failingTests.ToList())) {
          await options.OutputWriter.Status(line);
        }
      }
    }
    if (options.TestGenOptions.CoverageReport != null) {
      await new CoverageReporter(options).SerializeCoverageReports(coverageReport, options.TestGenOptions.CoverageReport);
    }
    if (TestGenerator.SetNonZeroExitCode) {
      exitValue = ExitValue.DAFNY_ERROR;
    }
    return exitValue;
  }
  

  private static async Task<bool> RunSingleTest(string header, string method) {
    var fullCode = header + method;
    var tempFile = Path.GetTempFileName() + ".dfy";
    await File.WriteAllTextAsync(tempFile, fullCode);

    try {
      string fileName = Environment.ProcessPath ?? "dafny";
      string arguments;
      string entryAssembly = Assembly.GetEntryAssembly()?.Location;

      if (Path.GetFileNameWithoutExtension(fileName).Equals("dotnet", StringComparison.OrdinalIgnoreCase) &&
          !string.IsNullOrEmpty(entryAssembly)) {
        arguments = $"\"{entryAssembly}\" test --no-verify \"{tempFile}\"";
      } else {
        arguments = $"test --no-verify \"{tempFile}\"";
      }

      var process = new Process {
        StartInfo = new ProcessStartInfo {
          FileName = fileName,
          Arguments = arguments,
          RedirectStandardOutput = true,
          RedirectStandardError = true,
          UseShellExecute = false,
          CreateNoWindow = true
        }
      };

      process.Start();

      var outputTask = process.StandardOutput.ReadToEndAsync();
      var errorTask = process.StandardError.ReadToEndAsync();

      await process.WaitForExitAsync();

      var output = await outputTask;
      var error = await errorTask;
      var fullOutput = output + "\n" + error;
      
      return process.ExitCode == 0 &&
             !fullOutput.Contains("FAILED") &&
             !fullOutput.Contains("expectation violation") &&
             !fullOutput.Contains("Error");
    }
    finally {
      if (File.Exists(tempFile)) {
        File.Delete(tempFile);
      }
    }
  }



public static async Task<HashSet<String>> GetUnverified(DafnyOptions options) {
    HashSet<String> unverified = [];
    object unverifiedLock = new object();
    
    if (options.Get(CommonOptionBag.VerificationCoverageReport) != null) {
      options.TrackVerificationCoverage = true;
    }

    var compilation = CliCompilation.Create(options);
    compilation.Start();

    var resolution = await compilation.Resolution;

    if (resolution != null) {
      var tcs = new TaskCompletionSource<bool>();
      var verification = compilation.VerifyAllLazily().ToObservable();

      verification.Subscribe(
        onNext: result => {
          bool verified = true;
          
          foreach (var taskResult in result.Results) {
            var outcome = taskResult.Result.Outcome;
            if (outcome != SolverOutcome.Valid && outcome != SolverOutcome.Bounded) {
              verified = false;
              break;
            }
          }

          if (!verified) {
            lock (unverifiedLock) {
              unverified.Add(result.CanVerify.FullDafnyName);
            }
          }
          
        },
        onError: ex => tcs.SetException(ex),
        onCompleted: () => tcs.SetResult(true)
        );
      
      await tcs.Task; 
    }

    return unverified;
  }

  internal static void PostProcess(DafnyOptions dafnyOptions, TestGenerationOptions.Modes mode) {
    dafnyOptions.CompilerName = "cs";
    dafnyOptions.Compile = true;
    dafnyOptions.RunAfterCompile = false;
    dafnyOptions.ForceCompile = false;
    dafnyOptions.DeprecationNoise = 0;
    dafnyOptions.ForbidNondeterminism = true;
    dafnyOptions.DefiniteAssignmentLevel = 2;
    dafnyOptions.UseBaseNameForFileName = false;
    dafnyOptions.VerifyAllModules = true;
    dafnyOptions.TypeEncodingMethod = CoreOptions.TypeEncoding.Predicates;
    dafnyOptions.Set(Snippets.ShowSnippets, false);
    dafnyOptions.TestGenOptions.Mode = mode;
  }
  
  public static readonly Option<bool> Simplify = new("--simplify",
    "Only for methods on Spec mode. Simplifies test output by including only input and output values." +
    "In other words, removes 'expect' statements related to pre and post condition, whenever possible.");
  
  public static readonly Option<bool> Fdnf = new("--fdnf",
    "Only for the Spec mode. It calculates the full DNF, instead of the safe DNF (default)." +
    "Produces all 2^N − 1 non-empty subsets of branch satisfaction. For A || B: branches A ∧ B, A ∧ !B, !A ∧ B." +
    "Generates more clauses (more test scenarios) but drops the short-circuit-safety guarantee: tests may evaluate " +
    "guarded subexpressions where the guard is false, potentially causing runtime errors" +
    "(out-of-bounds, division by zero) before the spec violation is reported.");
  
  public static readonly Option<bool> Bva = new("--bva",
    "Only for the Spec mode. Generates tests based on Boundary Value Analysis. Cannot be used simultaneously with --test-count.");

  public static readonly Option<uint> TestCount = new("--test-count", () => 1,
    "Number of tests to generate per method on Spec mode. 1 (default) generates a single test per method." +
    "Cannot be used simultaneously with --bva.");
  
  public static readonly Option<bool> IgnoreWarnings = new("--ignore-warnings",
    "Ignore warnings when generating tests.");
  
  public static readonly Option<bool> PassingFailing = new("--passing-failing",
    "Split generated tests into passing and failing.");

  public static readonly Option<uint> SequenceLengthLimit = new("--length-limit",
    "Add an axiom that sets the length of all sequences to be no greater than <n>. 0 (default) indicates no limit.");

  public static readonly Option<int> LoopUnroll = new("--loop-unroll", () => -1,
    "Higher values can improve accuracy of the analysis at the cost of taking longer to run.");

  public static readonly Option<string> PrintBpl = new("--print-bpl",
    "Print the Boogie code used during test generation.") {
    ArgumentHelpName = "filename"
  };
  public static readonly Option<string> ExpectedCoverageReport = new(["--expected-coverage-report",
    "--coverage-report"
    ],
    "Emit expected test coverage report to a given directory.") {
    ArgumentHelpName = "directory"
  };
  public static readonly Option<bool> ForcePrune = new("--force-prune",
    "Enable axiom pruning that Dafny uses to speed up verification. This may negatively affect the quality of tests.");
  static GenerateTestsCommand() {
    DafnyOptions.RegisterLegacyBinding(Simplify, (options, value) => {
      options.TestGenOptions.Simplify = value;
    });
    DafnyOptions.RegisterLegacyBinding(Fdnf, (options, value) => {
      options.TestGenOptions.Fdnf = value;
    });
    DafnyOptions.RegisterLegacyBinding(Bva, (options, value) => {
      options.TestGenOptions.Bva = value;
    });
    DafnyOptions.RegisterLegacyBinding(TestCount, (options, value) => {
      options.TestGenOptions.TestCount = value;
    });
    DafnyOptions.RegisterLegacyBinding(IgnoreWarnings, (options, value) => {
      options.TestGenOptions.IgnoreWarnings = value;
    });
    DafnyOptions.RegisterLegacyBinding(PassingFailing, (options, value) => {
      options.TestGenOptions.PassingFailing = value;
    });
    DafnyOptions.RegisterLegacyBinding(LoopUnroll, (options, value) => {
      options.LoopUnrollCount = value;
    });
    DafnyOptions.RegisterLegacyBinding(SequenceLengthLimit, (options, value) => {
      options.TestGenOptions.SeqLengthLimit = value;
    });
    DafnyOptions.RegisterLegacyBinding(PrintBpl, (options, value) => {
      options.TestGenOptions.PrintBpl = value;
    });
    DafnyOptions.RegisterLegacyBinding(ExpectedCoverageReport, (options, value) => {
      options.TestGenOptions.CoverageReport = value;
    });
    DafnyOptions.RegisterLegacyBinding(ForcePrune, (options, value) => {
      options.TestGenOptions.ForcePrune = value;
    });

    OptionRegistry.RegisterOption(LoopUnroll, OptionScope.Cli);
    OptionRegistry.RegisterOption(SequenceLengthLimit, OptionScope.Cli);
    OptionRegistry.RegisterOption(TestCount, OptionScope.Cli);
    OptionRegistry.RegisterOption(PrintBpl, OptionScope.Cli);
    OptionRegistry.RegisterOption(ExpectedCoverageReport, OptionScope.Cli);
    OptionRegistry.RegisterOption(ForcePrune, OptionScope.Cli);
    OptionRegistry.RegisterOption(IgnoreWarnings, OptionScope.Cli);
    OptionRegistry.RegisterOption(Simplify, OptionScope.Cli);
    OptionRegistry.RegisterOption(Fdnf, OptionScope.Cli);
    OptionRegistry.RegisterOption(Bva, OptionScope.Cli);
    OptionRegistry.RegisterOption(PassingFailing, OptionScope.Cli);
  }
}
