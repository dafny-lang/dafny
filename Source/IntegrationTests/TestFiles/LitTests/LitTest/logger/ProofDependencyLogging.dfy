// RUN: %baredafny verify --log-format:text --verify-included-files --allow-axioms --boogie -trackVerificationCoverage "%s" > "%t"
// RUN: %OutputCheck --file-to-check "%t" "%s"
// CHECK: Results for M.RedundantAssumeMethod \(correctness\)
// CHECK:     Proof dependencies:
// CHECK:       ProofDependencies.dfy\(177,12\)-\(177,16\): assume statement
// CHECK:       ProofDependencies.dfy\(178,5\)-\(178,17\): assertion always holds
//
// CHECK: Results for M.ContradictoryAssumeMethod \(correctness\)
// CHECK:     Proof dependencies:
// CHECK:       ProofDependencies.dfy\(183,12\)-\(183,16\): assume statement
// CHECK:       ProofDependencies.dfy\(184,12\)-\(184,16\): assume statement
//
// CHECK: Results for M.AssumeFalseMethod \(correctness\)
// CHECK:     Proof dependencies:
// CHECK:       ProofDependencies.dfy\(192,12\)-\(192,12\): assume statement
//
// CHECK: Results for M.ObviouslyContradictoryRequiresFunc \(well-formedness\)
// CHECK:     Proof dependencies:
// CHECK:       ProofDependencies.dfy\(198,12\)-\(198,16\): requires clause
// CHECK:       ProofDependencies.dfy\(199,12\)-\(199,16\): requires clause
//
// CHECK: Results for M.ObviouslyContradictoryRequiresMethod \(correctness\)
// CHECK:     Proof dependencies:
// CHECK:       ProofDependencies.dfy\(207,12\)-\(207,16\): requires clause
// CHECK:       ProofDependencies.dfy\(208,12\)-\(208,16\): requires clause
//
// CHECK: Results for M.ObviouslyRedundantRequiresFunc \(well-formedness\)
// CHECK:     Proof dependencies:
// CHECK:       ProofDependencies.dfy\(216,1\)-\(222,1\): function definition for ObviouslyRedundantRequiresFunc
// CHECK:       ProofDependencies.dfy\(217,12\)-\(217,16\): requires clause
// CHECK:       ProofDependencies.dfy\(219,11\)-\(219,15\): ensures clause
// CHECK:       ProofDependencies.dfy\(221,3\)-\(221,7\): function call result
// CHECK:       ProofDependencies.dfy\(221,5\)-\(221,5\): value always satisfies the subset constraints of 'nat'
//
// CHECK: Results for M.ObviouslyRedundantRequiresMethod \(correctness\)
// CHECK:     Proof dependencies:
// CHECK:       ProofDependencies.dfy\(225,12\)-\(225,16\): requires clause
// CHECK:       ProofDependencies.dfy\(227,11\)-\(227,15\): ensures clause
// CHECK:       ProofDependencies.dfy\(229,3\)-\(229,15\): assignment \(or return\)
// CHECK:       ProofDependencies.dfy\(229,12\)-\(229,12\): value always satisfies the subset constraints of 'nat'
//
// CHECK: Results for M.ObviouslyUnnecessaryRequiresFunc \(well-formedness\)
// CHECK:     Proof dependencies:
// CHECK:       ProofDependencies.dfy\(237,21\)-\(237,21\): value always satisfies the subset constraints of 'nat'
// CHECK:       ProofDependencies.dfy\(237,32\)-\(237,32\): value always satisfies the subset constraints of 'nat'
//
// CHECK: Results for M.ObviouslyUnnecessaryRequiresMethod \(correctness\)
// CHECK:     Proof dependencies:
// CHECK:       ProofDependencies.dfy\(244,25\)-\(244,25\): value always satisfies the subset constraints of 'nat'
// CHECK:       ProofDependencies.dfy\(244,48\)-\(244,48\): value always satisfies the subset constraints of 'nat'
//
// CHECK: Results for M.ObviouslyUnconstrainedCodeFunc \(well-formedness\)
// CHECK:     Proof dependencies:
// CHECK:       ProofDependencies.dfy\(248,1\)-\(256,1\): function definition for ObviouslyUnconstrainedCodeFunc
// CHECK:       ProofDependencies.dfy\(249,12\)-\(249,16\): requires clause
// CHECK:       ProofDependencies.dfy\(250,11\)-\(250,17\): ensures clause
// CHECK:       ProofDependencies.dfy\(252,7\)-\(252,7\): let expression binding
// CHECK:       ProofDependencies.dfy\(252,12\)-\(252,16\): let expression binding RHS well-formed
// CHECK:       ProofDependencies.dfy\(254,3\)-\(254,3\): function call result
//
// CHECK: Results for M.ObviouslyUnconstrainedCodeMethod \(correctness\)
// CHECK:     Proof dependencies:
// CHECK:       ProofDependencies.dfy\(259,12\)-\(259,16\): requires clause
// CHECK:       ProofDependencies.dfy\(260,11\)-\(260,17\): ensures clause
// CHECK:       ProofDependencies.dfy\(262,9\)-\(262,17\): assignment \(or return\)
// CHECK:       ProofDependencies.dfy\(264,3\)-\(266,8\): assignment \(or return\)
//
// CHECK: Results for M.PartiallyRedundantRequiresFunc \(well-formedness\)
// CHECK:     Proof dependencies:
// CHECK:       ProofDependencies.dfy\(270,1\)-\(275,1\): function definition for PartiallyRedundantRequiresFunc
// CHECK:       ProofDependencies.dfy\(271,23\)-\(271,27\): requires clause
// CHECK:       ProofDependencies.dfy\(272,11\)-\(272,15\): ensures clause
// CHECK:       ProofDependencies.dfy\(274,3\)-\(274,7\): function call result
// CHECK:       ProofDependencies.dfy\(274,5\)-\(274,5\): value always satisfies the subset constraints of 'nat'
//
// CHECK: Results for M.PartiallyUnnecessaryRequiresFunc \(well-formedness\)
// CHECK:     Proof dependencies:
// CHECK:       ProofDependencies.dfy\(279,22\)-\(279,26\): requires clause
// CHECK:       ProofDependencies.dfy\(282,21\)-\(282,21\): value always satisfies the subset constraints of 'nat'
// CHECK:       ProofDependencies.dfy\(282,32\)-\(282,32\): value always satisfies the subset constraints of 'nat'
//
// CHECK: Results for M.MultiPartRedundantRequiresFunc \(well-formedness\)
// CHECK:     Proof dependencies:
// CHECK:       ProofDependencies.dfy\(288,1\)-\(295,1\): function definition for MultiPartRedundantRequiresFunc
// CHECK:       ProofDependencies.dfy\(291,12\)-\(291,17\): requires clause
// CHECK:       ProofDependencies.dfy\(292,11\)-\(292,16\): ensures clause
// CHECK:       ProofDependencies.dfy\(294,3\)-\(294,3\): function call result
//
// CHECK: Results for M.MultiPartRedundantRequiresMethod \(correctness\)
// CHECK:     Proof dependencies:
// CHECK:       ProofDependencies.dfy\(300,12\)-\(300,17\): requires clause
// CHECK:       ProofDependencies.dfy\(301,11\)-\(301,16\): ensures clause
//
// CHECK: Results for M.MultiPartContradictoryRequiresFunc \(well-formedness\)
// CHECK:     Proof dependencies:
// CHECK:       ProofDependencies.dfy\(309,1\)-\(316,1\): function definition for MultiPartContradictoryRequiresFunc
// CHECK:       ProofDependencies.dfy\(310,12\)-\(310,16\): requires clause
// CHECK:       ProofDependencies.dfy\(311,12\)-\(311,16\): requires clause
// CHECK:       ProofDependencies.dfy\(313,11\)-\(313,16\): ensures clause
// CHECK:       ProofDependencies.dfy\(315,3\)-\(315,3\): function call result
//
// CHECK: Results for M.MultiPartContradictoryRequiresMethod \(correctness\)
// CHECK:     Proof dependencies:
// CHECK:       ProofDependencies.dfy\(319,12\)-\(319,16\): requires clause
// CHECK:       ProofDependencies.dfy\(320,12\)-\(320,16\): requires clause
// CHECK:       ProofDependencies.dfy\(322,11\)-\(322,16\): ensures clause
//
// CHECK: Results for M.CallContradictoryFunctionFunc \(well-formedness\)
// CHECK:     Proof dependencies:
// CHECK:       ProofDependencies.dfy\(336,1\)-\(342,1\): function definition for CallContradictoryFunctionFunc
// CHECK:       ProofDependencies.dfy\(337,12\)-\(337,16\): requires clause
// CHECK:       ProofDependencies.dfy\(338,11\)-\(338,15\): ensures clause
// CHECK:       ProofDependencies.dfy\(341,3\)-\(341,39\): function call result
// CHECK:       ProofDependencies.dfy\(341,3\)-\(341,35\): function precondition satisfied
//
// CHECK: Results for M.CallContradictoryMethodMethod \(correctness\)
// CHECK:     Proof dependencies:
// CHECK:       ProofDependencies.dfy\(345,12\)-\(345,16\): requires clause
// CHECK:       ProofDependencies.dfy\(348,9\)-\(348,47\): ensures clause at ProofDependencies.dfy\(333,12\)-\(333,16\) from call
// CHECK:       ProofDependencies.dfy\(348,9\)-\(348,47\): ensures clause at ProofDependencies.dfy\(333,21\)-\(333,25\) from call
// CHECK:       ProofDependencies.dfy\(348,9\)-\(348,47\): requires clause at ProofDependencies.dfy\(332,12\)-\(332,16\) from call
//
// CHECK: Results for M.FalseAntecedentRequiresClauseMethod \(correctness\)
// CHECK:     Proof dependencies:
// CHECK:       ProofDependencies.dfy\(357,3\)-\(357,15\): assignment \(or return\)
//
// CHECK: Results for M.FalseAntecedentAssertStatementMethod \(correctness\)
// CHECK:     Proof dependencies:
// CHECK:       ProofDependencies.dfy\(362,9\)-\(362,15\): assignment \(or return\)
// CHECK:       ProofDependencies.dfy\(363,20\)-\(363,24\): assertion always holds
//
// CHECK: Results for M.FalseAntecedentEnsuresClauseMethod \(correctness\)
// CHECK:     Proof dependencies:
// CHECK:       ProofDependencies.dfy\(368,21\)-\(368,25\): ensures clause
// CHECK:       ProofDependencies.dfy\(370,3\)-\(370,13\): assignment \(or return\)
//
// CHECK: Results for M.ObviouslyUnreachableIfExpressionBranchFunc \(well-formedness\)
// CHECK:     Proof dependencies:
// CHECK:       ProofDependencies.dfy\(373,1\)-\(380,1\): function definition for ObviouslyUnreachableIfExpressionBranchFunc
// CHECK:       ProofDependencies.dfy\(374,12\)-\(374,16\): requires clause
// CHECK:       ProofDependencies.dfy\(375,11\)-\(375,15\): ensures clause
// CHECK:       ProofDependencies.dfy\(379,8\)-\(379,12\): function call result
//
// CHECK: Results for M.ObviouslyUnreachableIfStatementBranchMethod \(correctness\)
// CHECK:     Proof dependencies:
// CHECK:       ProofDependencies.dfy\(383,12\)-\(383,16\): requires clause
// CHECK:       ProofDependencies.dfy\(384,11\)-\(384,15\): ensures clause
// CHECK:       ProofDependencies.dfy\(389,5\)-\(389,17\): assignment \(or return\)
//
// CHECK: Results for M.ObviouslyUnreachableMatchExpressionCaseFunction \(well-formedness\)
//
// CHECK:     Proof dependencies:
// CHECK:       ProofDependencies.dfy\(395,1\)-\(403,1\): function definition for ObviouslyUnreachableMatchExpressionCaseFunction
// CHECK:       ProofDependencies.dfy\(396,12\)-\(396,17\): requires clause
// CHECK:       ProofDependencies.dfy\(397,11\)-\(397,15\): ensures clause
// CHECK:       ProofDependencies.dfy\(401,15\)-\(401,15\): function call result
//
// CHECK: Results for M.ObviouslyUnreachableMatchStatementCaseMethod \(correctness\)
// CHECK:     Proof dependencies:
// CHECK:       ProofDependencies.dfy\(406,12\)-\(406,17\): requires clause
// CHECK:       ProofDependencies.dfy\(407,11\)-\(407,15\): ensures clause
// CHECK:       ProofDependencies.dfy\(411,15\)-\(411,23\): assignment \(or return\)
//
// CHECK: Results for M.ObviouslyUnreachableReturnStatementMethod \(correctness\)
// CHECK:     Proof dependencies:
// CHECK:       ProofDependencies.dfy\(416,12\)-\(416,17\): requires clause
// CHECK:       ProofDependencies.dfy\(417,13\)-\(417,17\): ensures clause
// CHECK:       ProofDependencies.dfy\(420,7\)-\(420,15\): assignment \(or return\)
// CHECK:     Unused by proof:
// CHECK:       ProofDependencies.dfy\(428,5\)-\(428,9\): assumption that divisor is always non-zero.
// CHECK:       ProofDependencies.dfy\(428,5\)-\(429,13\): calc statement result
//
// CHECK: Results for M.GetX \(well-formedness\)
// CHECK:     Proof dependencies:
// CHECK:       ProofDependencies.dfy\(446,5\)-\(446,5\): target object is never null

include "ProofDependencies.dfy"
