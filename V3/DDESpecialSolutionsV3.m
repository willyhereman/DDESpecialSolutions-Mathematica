
(* ************************************************************************ *)

(* : Title : DDESpecialSolutionsV2.m
*  : Authors : Douglas Baldwin, Unal Goktas, and Willy Hereman.
*    Department of Mathematical and Computer Sciences
*    Colorado School of Mines
*    Golden, Colorado 80401-1887, U.S.A.
*    Contact email: whereman@mines.edu or douglas@douglasbaldwin.com

*    Last updated: March 21, 2010 at 20:50 by Hereman in Boulder 
     Reason: 1. Replace the old AnalyzeSolve (dated January 13, 2003) by 
                AnalyzeSolve V2 written by Doug Baldwin (dated March 13, 2010) 
             2. Minor fixes marked with WH:03/17/2010. 

*  : Previously updated : Sunday, January 25, 2009 at 01:30 AM by Hereman
*  : Previous update : Saturday, January 10, 2009 at 10:21 P.M. by Baldwin
*  : Summary : Solves systems of nonlinear differential-difference equations
     (DDEs) also called lattices, in terms of the hyperbolic function Tanh.
*  : Warnings : This package uses the assumption that Sqrt[a^2] -> a, etc.
*    (see MySimplificationRules below) when simplifying. *)

(* ************************************************************************ *)

(* ------------------------------------------------------------------------- *)
(* Algorithm and implementation by Douglas Baldwin, *)
(* Unal Goktas (WRI) and Willy Hereman. *)
(* Copyright 2009 *)

BeginPackage["Calculus`DDESpecialSolutions`"]

Unprotect[DDESpecialSolutions]

(* Define Messages and Usage *)

DDESpecialSolutions::usage = 
"DDESpecialSolutions[eqns, funcs, dvars, cvars, params, opts] solves a "<>
"system of nonlinear differential-difference equations for funcs, with "<>
"continuous independent variables cvars ({x,y,z,...}), discrete independent "<>
"variables dvars ({n,m,...}) and non-zero parameters params in terms of "<>
"hyperbolic tangent functions."

DDESpecialSolutions::poly = 
"This system must be a polynomial of fixed order."

DDESpecialSolutionsmSolver::freedom = 
"Freedom exists in this system, as `1` are both dominant "<>
"powers in expression `2`."

DDESpecialSolutions`dominantBehavior::freevalues = 
"The solution(s) `1` do not fix all the values of \!\(M\_i\).  
We will now generate all the possible values for the free \!\(M\_i\) "<>
"up to the user-supplied option MaxDegreeOfThePolynomial which is set to 3 "<>
"by default, but can be any non-negative integer."

DDESpecialSolutions`dominantBehavior::underdetermined = 
"There is too much freedom in choosing the values of \!\(M\_i\). "<>
"We will now generate all the possible values for the free \!\(M\_i\) "<>
"from zero to the user-supplied option MaxDegreeOfThePolynomial "<>
"(with default 3), but can be any integer."

DDESpecialSolutionsmSolver::DegreeOfThePolynomial = 
"Algorithm continuing with user-supplied exponent of the polynomial `1`."

DDESpecialSolutionsmSolver::remove = 
"The potential solutions `1` are being removed because they are "<>
"(i) negative, "<>
"(ii) contain freedom, "<>
"(iii) fail to balance highest exponent terms from two "<>
"different terms in the original system.  If \!\(M\_i\) < 0, then the "<>
"transformation u -> 1/v may result in a system that DDESpecialSolutions "<>
"can solve."

DDESpecialSolutionsBuildSystem::fail = 
"The systems of equations was inconsistent under the assumption that "<>
"\!\(a\_\(i,M\_i\) \[NotEqual] 0\), please check the \!\(M\_i\) values "<>
"by hand."

DDESpecialSolutions::solve = 
"The algorithm failed while attempting to find the coefficients for "<>
"the polynomial solution."

(* Options definition. *)

(* WH:01/23/2009 replaced symbolic test flag to True *)
Options[DDESpecialSolutions] = 
  { Verbose -> False, 
    InputForm -> False, 
    NumericTest -> True,
    SymbolicTest -> True, 
    DegreeOfThePolynomial -> {},
    MinDegreeOfThePolynomial -> 1, 
    MaxDegreeOfThePolynomial -> 3, 
    SolveAlgebraicSystem -> True
  }

Begin["`Private`"]

(* If called with non-lists, makes them lists. *)

DDESpecialSolutions[eqns_?(!ListQ[#]&), funcs_, dvars_, cvars_, param_, 
  opts___?OptionQ]:=
  DDESpecialSolutions[{eqns}, funcs, dvars, cvars, param, opts]

DDESpecialSolutions[eqns_, funcs_?(!ListQ[#]&), dvars_, cvars_, param_, 
  opts___?OptionQ]:=
  DDESpecialSolutions[eqns, {funcs}, dvars, cvars, param, opts]

DDESpecialSolutions[eqns_, funcs_, dvars_?(!ListQ[#]&), cvars_, param_, 
  opts___?OptionQ]:=
  DDESpecialSolutions[eqns, funcs, {dvars}, cvars, param, opts]

DDESpecialSolutions[eqns_, funcs_, dvars_, cvars_?(!ListQ[#]&), param_, 
  opts___?OptionQ]:=
  DDESpecialSolutions[eqns, funcs, dvars, {cvars}, param, opts]

DDESpecialSolutions[eqns_, funcs_, dvars_, cvars_, param_?(!ListQ[#]&),
  opts___?OptionQ]:=
  DDESpecialSolutions[eqns, funcs, dvars, cvars, {param}, opts]

(* ************************************************************************ *)

(* Start of functions. *)

DDESpecialSolutions[eqns_List, funcs_List, dvars_List, cvars_List,
    param_List, opts___?OptionQ]:=
  Block[
    { testarg = FreeQ[MapAll[Expand, eqns], (Power[b__, a__] /; 
        (!FreeQ[a, _Symbol] | MemberQ[b, _Real | _Integer])) ],
      numberOfEquations,
      VerboseTest = Verbose /. {opts} /. Options[DDESpecialSolutions],
      time = TimeUsed[],
      system,
      mSoln,
      newSystem,
      solution
    }, (* Protected Local Variables *)

  numberOfEquations = Length[eqns];
     
  If[!testarg, Message[DDESpecialSolutions::poly]];
  (
    (* If verbose, prints system. *)
    If[VerboseTest,
      Print["The given system of differential-difference equations is: "];
      Print[ eqns /.
        {Derivative[n__][F_][x__]:>
          SequenceForm[F,
            Subscript[SequenceForm @@
              { Sequence @@ ({x} /. ((# -> Sequence[])& /@ cvars)),
                ";",
                Sequence @@ 
                  Flatten[
                    Table[
                      #[[1]], {#[[2]]}
                    ]& /@ Transpose[{{x}, {n}}]
                  ]
              }
            ]
          ],
          Sequence @@ (
            (#[x__] :> 
              Subscript[
                #, 
                Sequence @@ ({x} /. ((# -> Sequence[])& /@ cvars))
              ]
            )& /@ funcs)
        }
      ]
    ];

    (* Step D1 in the paper. *)
    (* Transforms the DDE into a nonlinear DDE in $T$ *)
    If[VerboseTest,
      Print["Transforming the system of differential-difference equations "<>
            "into a nonlinear system of DDEs in T = Tanh."]
    ];

    system = 
      DDESpecialSolutionsVarChange[
        eqns /. (a__==b__):>(a-b),
        funcs, 
        dvars, 
        cvars
      ];

    If[VerboseTest,
      Print[CleanUpFunction[system /. myTrackingVariable[_]->1]];
      Print["Time Used:", TimeUsed[]-time]
    ];

    time = TimeUsed[];

    (* Step D2 in the paper. *)
    (* Determines the maximal degree of the polynomial solutions. *)
    If[VerboseTest,
      Print["Determining the maximal degree of the polynomial solutions in T."]
    ];

    mSoln =
      Internal`DeactivateMessages[
        DDESpecialSolutionsmSolver[system, dvars, cvars, opts], 
        Solve::svars
      ];
    
    If[VerboseTest,
      Print[CleanUpFunction[
      DeleteCases[
         mSoln, 
         max[_]->_, 
         2]
           ]
           ];
      Print["Time Used:", TimeUsed[]-time]
    ];

    time = TimeUsed[];

    (* Step D3 in the paper. *)
    (* Derives the nonlinear algebraic system for the coefficients $a_{ij}$. *)
(* WH:03/17/2010 print statement was out of sequence, moved it lower *)
(* 
    If[VerboseTest,
      Print["Deriving the nonlinear algebraic system for the coefficients."]
    ];
*)
    newSystem = 
      DDESpecialSolutionsBuildSystem[mSoln, system, dvars, cvars, param, opts];
    If[VerboseTest,
      Print["Deriving the nonlinear algebraic system for the coefficients."]
    ];

    If[VerboseTest,
      Print["The nonlinear algebraic system is: "];
      Print[CleanUpFunction[newSystem ]];
      Print["Time Used:", TimeUsed[]-time]
    ];

    (* DB:07/23/2004 Output algebraic system. *)
    If[!(SolveAlgebraicSystem /. {opts} /. Options[DDESpecialSolutions]),
      Return[CleanUpFunction[newSystem]];
    ];

    time = TimeUsed[];

    (* Step D4 in the paper. *)
    (* Solve the nonlinear parameterized system. *)
    If[VerboseTest,
      Print["Solving the nonlinear algebraic system."]
    ];

    solution = 
      Algebra`AnalyzeAndSolve`AnalyzeAndSolve @@ #& /@ newSystem;

    (* DB:01/10/2009 Add simplification of solution *)
    solution = 
      solution /. 
        { Tanh[x_]^2/((-1 + Tanh[y_])*(1 + Tanh[z_])) :> 
            - Sinh[x]^2 /; x == y == z
        };

    If[Length[Flatten[solution]] === 0,
      Message[DDESpecialSolutions::solve];Return[{}];
    ];

    If[VerboseTest,
      Print[CleanUpFunction[solution]];
      Print["Time Used:", TimeUsed[]-time]
      ];

    time = TimeUsed[];

    (* WH:03/17/2010: the solution may contain a condition on Tanh[c[1]] *)
    (*                send a warning to the user *)
    If[ 
       Cases[solution, x: ( Tanh[c[_]] -> _), Infinity] != {}, 
            CellPrint[
             Cell[
                  "Some of the solutions of the algebraic system impose " <>
                  "conditions on the Tanh[c[i]]. ",
                  "Message"
             ]
            ];
            CellPrint[
             Cell[
                  "Ignoring such conditions, the corresponding solutions " <> 
                   ToString[ InputForm[ CleanUpFunction[funcs] ] ] <> 
                  " will be build (and tested, if requested).", 
              "Message"
             ]
            ]
    ]; (* end if *)

    (* Step D5 in the paper. *)
    (* Build and test the solitary wave solutions. *)
    (* WH:03/17/2010, changed the logic a little *)
    If[VerboseTest,
      If[( !(NumericTest /. {opts} /. Options[DDESpecialSolutions]) &&
           !(SymbolicTest /. {opts} /. Options[DDESpecialSolutions]) ),
        Print["Building the travelling wave solutions (without testing)."], 
        (* else *)
        Print["Building and (numerically and/or symbolically) testing "<>
              "the travelling wave solutions."]
      ]
    ];

    solution = 
    DDESpecialSolutionsBuildSolutions[solution, mSoln, eqns, funcs, 
       dvars, cvars, param, opts];

    (* DB:01/10/2009 Remove {}. *)
    solution = Replace[solution, {} -> Sequence[], 1];

(* WH:03/17/2010 replace the print statements *)
(*
    If[VerboseTest,
      Print[CleanUpFunction[solution]];
      Print["Time Used:", TimeUsed[]-time];
      Print[];
     If[( (SymbolicTest /. {opts} /. Options[DDESpecialSolutions]) ||
          (NumericTest /. {opts} /. Options[DDESpecialSolutions]) ),
       Print["The (numerically and/or symbolically) tested solutions:"],
       Print["The possible non-trivial solutions (before any testing) are:"]
      ];
    ];
*)
(* by the following: *)

    (* start if 10 *)
    If[VerboseTest,
      Print["Time Used:", TimeUsed[]-time];
      Print[];
      (* WH:03/17/2010 adjusted the print statements *)
      Which[
        ( ( NumericTest /. {opts} /. Options[DDESpecialSolutions] ) &&
          !( SymbolicTest /. {opts} /. Options[DDESpecialSolutions] ) ),
        Print["The final solutions were only tested numerically."],
        ( (SymbolicTest /. {opts} /. Options[DDESpecialSolutions]) &&
          !( NumericTest /. {opts} /. Options[DDESpecialSolutions] ) ),
        Print["The final solutions were only tested symbolically."],
        ( ( NumericTest /. {opts} /. Options[DDESpecialSolutions] ) && 
        ( SymbolicTest /. {opts} /. Options[DDESpecialSolutions] ) ),
        Print["The final solutions were tested both numerically "<> 
              "and symbolically."],
        ( !( NumericTest /. {opts} /. Options[DDESpecialSolutions] ) &&
          !( SymbolicTest /. {opts} /. Options[DDESpecialSolutions] ) ),
         Print["The list of possible final solutions (without "<>
               "testing them numerically or symbolically):"]
      ] (* end of which *)
     ]; (* end if 10 *)

    (* Returns solutions to user. *)
    Return[
      If[InputForm /. {opts} /. Options[DDESpecialSolutions],
        InputForm[CleanUpFunction[solution]],
        CleanUpFunction[solution]
      ]
    ];

  ) /; testarg
  ] /; FreeQ[funcs, Alternatives @@ Join[dvars, cvars] ];
  (* end of block DDESpecialSolutions *)

(* ************************************************************************ *)

(* : Title : DDESpecialSolutionsVarChange *)
(* : Author : Douglas Baldwin *)
(* : Input : The equation list (F[i][n,t]) and the form tanh. *)
(* : Output : The system in the form u[i][T] *)
(* : Summary : Converts from real space-time domain to u[i][T]. *)

DDESpecialSolutionsVarChange[eqns_List, funcs_List, dvars_List, cvars_List]:=
  Block[{ varChangeDebug = False,
          funcRules, (* conversion to T *)
          i=0, (* Iterator for myTrackingVariables *)
          eqList, (* The list of equations, in a usable form *)
          system (* The system after transform to DDE in T *)
        }, (* Protected Local Variables *)

    (* Creates a set of rules to converts the users functions *)
    (* (e.g., u[n,t]) to varChangeFunction[i][n,t]. *)
    funcRules = 
      Table[
        funcs[[i]] -> varChangeFunction[i],
        {i, Length[funcs]}
      ];

    (* Adds tacking variables which will be used in the mSolve *)
    (* function to check for false balances coming form a single *)
    (* term. *)
    eqList = 
      If[Head[#] === Plus, 
        Plus @@ ((myTrackingVariable[++i]*#) & /@ List @@ #),
        myTrackingVariable[++i]*#] & /@ Expand[eqns];
     
    (* Converts the user functions to varChangeFunction[i]. *)
    eqList = eqList //. funcRules;

    (* Changes the space of the functions. *)
    system = eqList /. 
      {
      varChangeFunction[n_][var__] :> 
        phi[n][
          Sequence @@ Select[{var}, FreeQ[#,  Alternatives @@ cvars] &] 
        ][
          Sum[c[i]*{var}[[i]], 
            {i, Length[{var}]}
          ]
        ], 
       Derivative[temp__][varChangeFunction[n_]][var__] :>  
         (
           D[
            phi[n][
              Sequence @@ Select[{var}, FreeQ[#,  Alternatives @@ cvars] &] 
            ][
              Sum[c[i]*{var}[[i]], 
                {i, Length[{var}]}
              ]
            ],
            Sequence @@ 
              Transpose[{Evaluate[{var} /. a_ + _Integer :> a], {temp}}]
           ]
         )
      };

    If[varChangeDebug,
      Print["After changing to a traveling frame: "];
      Print[CleanUpFunction[ system ]];
    ];

    (* Parameterizes the sequence $ c_1 x + c_2 y +...\to \eta $ *)
    system = system /. 
      {
        phi[n_][shifts__][__] :> phi[n][shifts][T],
        Derivative[i_][phi[n_][shifts__]][__] :> 
            Derivative[i][phi[n][shifts]][T]
      };

    (* Repeatedly applies the chain rule. *)
      system = system /. 
        { Derivative[a_][phi[n_][shifts__]][T] :> 
            Expand[
              Nest[(1-T^2)*D[#, T]&, 
                u[n][shifts][T], 
                a
              ]
            ],
          phi[n_][shifts__][T] :> u[n][shifts][T]
        };

    If[varChangeDebug,
      Print["After substituting the correct form: "];
      Print[CleanUpFunction[ system ]];
    ];

    (* Simplifies the system by removing extra factors (1-T^2)'s *)
    (* and powers of T from the system. *)
    system = 
      If[(# /. T->-1) === 0 && (# /. T->1) === 0, 
        Factor[#/(1-T^2)], Factor[#]]& /@ system;
    system = 
      If[(# /. T->0) === 0, 
        Factor[#/T], Factor[#]]& /@ system;

    If[varChangeDebug,
      Print["After removing possible common factors (1-T^2)^k and T^j:"];
      Print[CleanUpFunction[ system ]];
    ];

    (* Returns the system back to the DDESpecialSolutions *)
    Return[MapAll[Factor, system]];
  ]; (* end of block DDESpecialSolutionsVarChange *)

(* ************************************************************************ *)

(* : Title : DDESpecialSolutionsmSolver *)
(* : Author : Douglas Baldwin *)
(* : Date : Sunday, December 15, 2002 *)
(* : Input : The system generated by varChange. *)
(* : Output : The power of the polynomial solutions for u[i][T], id est 
     u[i][T] = a[1,0]+a[1,1]*T+a[1, 2]*T^2+...+a[1,n]*T^n. *)

DDESpecialSolutionsmSolver[system_List, dvars_, cvars_, opts___?OptionQ] :=
  Module[{mSoln},
    mSoln = 
      { ToExpression[
          StringReplace[            
            ToString[DegreeOfThePolynomial /. {opts}],
            {"m" -> "Calculus`DDESpecialSolutions`Private`m",
             "n" -> "Calculus`DDESpecialSolutions`Private`n"
            }
          ]
        ]
      }; 
    Message[DDESpecialSolutionsmSolver::DegreeOfThePolynomial, 
      CleanUpFunction[mSoln]
    ];
    Return[mSoln];
   ] /; (DegreeOfThePolynomial /. {opts} /. 
     Options[DDESpecialSolutions]) =!= {};
   (* end of module DDESpecialSolutionsmSolver *)

DDESpecialSolutionsmSolver[system_List, dvars_, cvars_, opts___?OptionQ] :=
  Module[{mSolverDebug = False, (* Debugging Boolean flag *)
          myTrackingVariableMax, (* Max Tracking Variable. *)
          eqnList, (* The result of the system generation function. *)
          mList0, mList, (* Lists of the powers of F in m_i. *)
          mSoln (* List of explicit solutions for m_i. *)
         },

    (* Determines max{i : myTrackingVariables[i]} by *)
    (* applying a rule to system which sets myTrackingVariable *)
    (* in the process.  *)
    myTrackingVariableMax = 0;
    system /. myTrackingVariable[a_Integer] :> 
      myTrackingVariable[
        If[a > myTrackingVariableMax, 
           myTrackingVariableMax = a
          ]; 
      a];

    (* Substitutes the ansatz chi*F^{m_i} for u,v,...,w *)
    eqnList = 
      mSolve`SystemGeneration[system, dvars, cvars, myTrackingVariableMax];

    If[mSolverDebug,
      Print["eqnList, System after substitution of the ansatz: "];
      Print[CleanUpFunction[eqnList]];
    ];

    (* Pulls off the expressions for m_i *)
    mList0 = mSolve`ListFormation[#, myTrackingVariableMax]& /@ eqnList;

    If[mSolverDebug,
      Print["mList0, Exponents of F before simplification: "];
      Print[CleanUpFunction[mList0]];
    ];

    (* Removes expressions which cannot be the highest power *)
    (* by trackingVariable. *)
    mList = 
      Flatten[mSolve`Simplification /@ #]& /@ #& /@ mList0;

    If[mSolverDebug,
      Print["mList, Exponents after simplification (from mList0): "];
      Print[CleanUpFunction[mList]];
      Print["Transpose[{mList, mList0}] yields: "];
      Print[CleanUpFunction[ Transpose[ {mList, mList0} ] ]];
    ];

    mSoln = 
      Union @@ (* DB:01/10/2009 Changed Join to Union. *)
        ( mSolve`FindBalance[#[[1]], #[[2]], eqnList, opts ]& /@ 
            Transpose[ {mList, mList0} ]
        );

    If[mSolverDebug,
      Print["The solutions for the exponents are: "];
      Print[CleanUpFunction[ mSoln ]];
    ];

    (* If it doesn't find any solutions, it quits. *)
    If[Length[mSoln] == 0,
      StylePrint[
        "The algorithm failed while attempting to find a positive values "<>
        "of \!\(M\_i\).  The list of rules that constrain the system are " <>
        ToString[ InputForm[ CleanUpFunction[mRules] ] ] <>
        ".  The original powers in \!\(M\_i\) are " <>
        ToString[ InputForm[ CleanUpFunction[mList] ] ] <>
        ".",
        "Message"
      ];
      Abort[]
    ];

    If[mSolverDebug,
      Print["mSoln, the final version before being returned: "];
      Print[CleanUpFunction[mSoln]];
    ];  

    (* Returns the solutions. *)
    Return[mSoln];

  ] /; (DegreeOfThePolynomial /. {opts} /. 
     Options[DDESpecialSolutions]) === {};
  (* end of module DDESpecialSolutionsmSolver *)

(* Breaks up the system into the correct form. *)
mSolve`SystemGeneration[system_, dvars_, cvars_, myTrackingVariableMax_] :=
  Block[{SystemGenerationDebug = False,
          listOfShifts = {}, (* List of discrete shifts. *)
          mySystem = MapAll[Expand, system], 
                  (* The system passed to the function after *)
                  (* transformation. *)
          i = 1, (* Iterator. *)
          replacementRule, (* The rule to be used on the system. *)
          eqnList (* The result which will be returned. *)
         },

    (* Generate list of shifts. *)
    (* Modified DB:10/15/2003 *)
    system /. u[_][a__] :> (listOfShifts = Append[listOfShifts, {a}]; 0);
    listOfShifts = Union[listOfShifts];

    If[SystemGenerationDebug,
      Print["The list of shifts: "];
      Print[CleanUpFunction[ listOfShifts ]];
    ];

    (* Creates the replacement piece for the next function. *)
    (* DB:10/04/2003 since the shifts do not contribute, *)
    (* we set those terms to a constant. *)
    replacementRule = 
    Join[{ u[n_][Sequence @@ #] :> Function[ {F},\[Chi][n]*F^m[n] ],
        u[n_][__] :> Function[ {F}, \[Chi][n] ]}& /@ listOfShifts,
        (* DB:01/09/2009 When the DDE contains (u[i][n+p] \pm u[i][n-p]) *)
        (* then power can be either \[Chi][i] or \[Chi][i]*F^(-1). *)
        { u[n_][Sequence @@ #] :> Function[ {F}, \[Chi][n]*F^m[n] ],
        u[n_][__] :> Function[ {F}, \[Chi][n]*F^-1 ]}& /@ listOfShifts
        ];

    If[SystemGenerationDebug,
      Print["The replacement rule for the system:"];
      Print[CleanUpFunction[ replacementRule ]];
    ];

    (* Replaces the function u[i_] with a function in *)
    (* F^m[i] or F^n[i]. *)
    eqnList = 
      Expand[
        DeleteCases[
          Flatten[
            mySystem /. 
              #
          ], 
          0
        ]
      ]& /@ replacementRule;

    If[SystemGenerationDebug,
      Print["The system after substitution of chi*F^{m_i}: "];
      Print[CleanUpFunction[eqnList]];
    ];

    (* Returns the list after substitution of the ansatz. *)
    Return[Replace[eqnList, {} -> Sequence[], 1]];
  ]; (* end of block mSolve`SystemGeneration *)

mSolve`ListFormation[eqnList0_, myTrackingVariableMax_]:=
  Block[{ mPowerListFormationDebug = False,
          eqnList = eqnList0,
          mList
         },

    (* Modify eqnList0 so that it is easier for the Exponents *)
    (* function to deal with. DB:10/02/2003 *)
    eqnList = 
      Together /@ MapAll[Expand, eqnList0];

    If[mPowerListFormationDebug,
      Print["The system after some simplifications: "];
      Print[CleanUpFunction[ eqnList ]];
    ];

    (* Pulls off the exponents of T and forms a list *)
    (* of expressions of the form {{{1+m[1]},{..}..}..}  *)
    mList = 
      Union[
        Exponent[#, T, List]
      ]& /@ eqnList0;

    (* DB:01/09/2009 Remove constant exponents. *)
    mList = Select[#, ! FreeQ[#, m[_]] &] & /@ mList;

    If[mPowerListFormationDebug,
      Print["The list of powers of F: "];
      Print[CleanUpFunction[mList]];
    ];

    eqnList = 
      ( Table[
          Coefficient[#, myTrackingVariable[i] ], 
          {i, 1, myTrackingVariableMax}
        ]& /@ eqnList0
      ) /. 0:>Sequence[];

    If[mPowerListFormationDebug,
      Print["The system further being subdivided: "];
      Print[CleanUpFunction[eqnList]];
    ];

    (* Breaks up expressions into lists of terms. *)
    eqnList = 
      If[Head[#]===Plus, List @@ #, {#}]& /@ #& /@
        MapAll[Expand, eqnList];

    If[mPowerListFormationDebug,
      Print["The system after plus (+) is replaced by {} using + -> {} is: "];
      Print[CleanUpFunction[eqnList]];
    ];

    (* Pulls off the exponents of T and forms a list *)
    (* of expressions of the form {{{1+m[1]},{..}..}..}  *)
    (* DB:05/15/2004 moved Union. *)
    (* DB:01/09/2009 Replaced "/. 0:> Sequence[]" using Select. *)
    mList = 
      ( Select[#, ! FreeQ[#, m[_]] &] & /@
        ( Union[ Exponent[#, T] ]& /@ # )
      )& /@ eqnList;
    
    If[mPowerListFormationDebug,
      Print["The list of powers of F: "];
      Print[CleanUpFunction[mList]];
    ];

   (* Returns the number of equations and the list of powers. *)
   Return[mList];
  ]; (* end of block mSolve`List *)

mSolve`Simplification[mList0_]:=
  Module[{mPowerListSimplificationDebug = False,
          mList, (* The list of powers. *)
          mListStructure (* Structure of powers. *)
         }, (* Protected Local Variables. *)

    (* The following lines breaks up the list of exponents *)
    (* of T and then removes invalid cases. *)

    (* Breaks up the expressions of $a+b \, m_i+c\, m_j+...$ *)
    (* where $a,b,c,...,i,j,k,...\in\mathbb{R}$ into lists. *)
    mList = 
      If[Head[#]===Plus, 
        List @@ #, 
        If[(Head[#]===m || Head[#]===n) || Head[#]===Times, 
          {#}, 
          #
        ]
      ]& /@ mList0;

    If[mPowerListSimplificationDebug,
      Print["Breaks up $a + b m_i + c m_j +...$ into lists: "];
      Print[CleanUpFunction[mList]];
    ];

    (* The following routine strips off the $a$ in the above *)
    (* expression and leaves only the underlying structure. *)
    mListStructure = Union[mList /. {a_Integer, b__}:>{b}];

    If[mPowerListSimplificationDebug,
      Print["The above without $a$: "];
      Print[CleanUpFunction[ mListStructure ]];
    ];

    (* Re-organizes the list of powers of T by the structure *)
    (* listed above. *)
    mList = 
      Cases[mList, {_, Sequence @@ #} | #]& /@ mListStructure;

    If[mPowerListSimplificationDebug,
      Print["The list of powers reorganized by structure: "];
      Print[CleanUpFunction[mList ]];
    ];

    (* Determines the maximum $a$ in each power of T *)
    mList = 
      {Max[# /. {a_, ___}:>If[IntegerQ[a], a, 0]& /@ #]}& /@ mList;

    If[mPowerListSimplificationDebug,
      Print["The list of powers (after the powers which cannot be "<>
            "the highest power are removed): "];
      Print[CleanUpFunction[mList ]];
    ];

    (* Creates a list of the maximum powers of T, such *)
    (* that all the members of the list are of the form *)
    (* $a_{\rm max}+b\,m_i+c\,m_j+...+d\,m_i\,m_j$ *)
    mList = 
      (Plus @@ Flatten[#])& /@ 
        Transpose[{mList, mListStructure}];

    If[mPowerListSimplificationDebug,
      Print["Formulates the powers into the correct form: "];
      Print[CleanUpFunction[mList ]];
    ];

    (* Returns the simplified list. *)
    Return[mList];
 ]; (* end of module mSolve`Simplification *)

mSolve`FindBalance[mList_List, mList0_List, eqnList_List, opts___?OptionQ ]:=
  Module[{ mSolverDebug = False,
           myMList, (* List of m_i's:  {m_1, m_2, m_3, ...} *)
           mRules, (* Rules for m_i, such as m_1 -> m_2. *)
           mSoln, mSoln0 (* List of explicit solutions for m_i. *)
         }, (* Protected Local Variables *)

    (* Forms a list of all the m_i. *)
    myMList = {};
    mList /. 
      m[i_Integer] :> (myMList = Append[myMList, m[i]];m[i]);
    myMList = Union[myMList];

    If[mSolverDebug,
      Print["The $m_i$s to be solved for are: "];
      Print[CleanUpFunction[myMList]];
    ];

    (* Solves the expressions of m_i for m_i *)
    mRules = mSolve`RulesSolver[#, myMList]& /@ mList;

    If[mSolverDebug,
      Print["mRules, the solution iteration yields: "];
      Print[CleanUpFunction[mRules]];
    ];  

    (* Uses the previous results to determine *)
    (* explicit solutions for m_i. *)
    mSoln0 = mSolve`PowerSolver[mRules, myMList];

    If[mSolverDebug,
      Print["mSoln, the possible solutions before pruning: "];
      Print[CleanUpFunction[mSoln0]];
    ];  

    (* DB:07/23/2004 New version from PDESpecialSolutions code. *)
    mSoln =   
      Join[ mSoln0, mSolve`FixFreeM[mSoln0, myMList, opts]];

    (* Remove bad solutions. *)
    mSoln  = 
      mSolve`SystemCleanUp[eqnList, mList, mSoln0, myMList];

    (* DB:03/21/2003 warn the user when potential solutions are removed. *)
    If[Length[Complement[Union[Sort /@ mSoln0], mSoln] ] > 0,
      Message[DDESpecialSolutionsmSolver::remove, 
        CleanUpFunction[Complement[Union[Sort /@ mSoln0], mSoln] ]
      ];
    ];

    If[mSolverDebug,
      Print["mSoln, the possible solutions after pruning: "];
      Print[CleanUpFunction[mSoln]];
    ];  

    (* Returns the solutions. *)
    Return[mSoln];
  ]; (* end of module mSolve`FindBalance *)

mSolve`RulesSolver[mList0_, myMList_]:=
  Module[{rulesSolverDebug = False,
          mList,
          eqnList,
          mRules (* List of rules from first solve. *)
         }, (* Protected local variables. *)

    (* Makes sure it is the simplest list possible *)
    (* for combinatorial purposes. *)
    mList = Union[mSolve`Simplification[mList0] ];

    If[rulesSolverDebug,
      Print["The mList (used in the Power Solver routine) is: "];
      Print[CleanUpFunction[mList]];
    ];    

    (* Forms a list of equations to be solved for m_i. *)
    eqnList =   
      Flatten[
        Map[
          Thread[
            Table[#[[1]], {Length[#] -1} ] == Drop[#, 1]
          ]&,
          Table[Drop[mList, i], 
            {i, 0, Length[mList] - 2}
          ]
        ],
        1
      ];

    If[rulesSolverDebug,
      Print["The equation(s) to be solved first: "];
      Print[CleanUpFunction[eqnList]];
    ];    

    (* Does the first run of solving. *)
    mRules = 
      Union[
        Flatten[
          Solve[#, myMList]& /@ eqnList
        ]
      ];

    If[rulesSolverDebug,
      Print["The first set of solutions: "];
      Print[CleanUpFunction[mRules]];
    ];    

    Return[mRules];
  ]; (* end of module mSolve`RulesSolver *)

mSolve`PowerSolver[mRules0_, myMList_]:=
  Module[{powerSolverDebug = False,
          mRules = Sort[mRules0, (Length[#1] < Length[#2])&],
          numberOfEquations = Length[myMList]
         }, (* Protected local variables. *)

    If[powerSolverDebug,
      Print["The mRules used in the Power Solver routine (sorted from " <>
            "shortest to longest) is: "];
      Print[CleanUpFunction[mRules]];
    ];    

    (* Forms a list of equations to be solved for m_i. *)
    eqnList = 
      Outer[List, Sequence @@ (mRules /. Rule->Equal)] ;

    (* Since Outer creates a list numberOfEquations deep, we *)
    (* drop it down into the correct form. DB:05/20/2003 *)
    eqnList = 
      Partition[ Flatten[ eqnList ], numberOfEquations ];
    
    If[powerSolverDebug,
      Print["The next set of equations to be solved: "];
      Print[CleanUpFunction[eqnList]];
    ];   

    (* Takes these solutions and uses them to find *)
    (* actual integer solutions to $m_i$ *)
    mSoln = 
      Union[
        Sequence @@ 
          Solve[#, myMList]& /@ eqnList
      ];

    If[powerSolverDebug,
      Print["The solutions are: "];
      Print[CleanUpFunction[mSoln]];
    ];

   (* Returns the solutions *)
   Return[mSoln];
  ]; (* end of module mSolve`PowerSolver *)

mSolve`SystemCleanUp[eqnList0_, mList_, mSoln0_, myMList_]:=
  Module[{systemCleanUpDebug = False, (* The debug flag. *)
          mSoln = Union[Sort /@ mSoln0], (* A local version of mSoln0. *)
          chiList = {}, (* The list of chi constraints. *)
          eqnList, (* A local copy of the equations. *)
          numberOfEquations = Length[eqnList0] (* The number of equations. *)
         }, (* Protected local variables. *)

     (* Applies the solutions to the expressions of m_i. *)
     mSoln = 
      Transpose[{(mList //. #)& /@ mSoln, mSoln}];

     If[systemCleanUpDebug,
       Print["The expressions of m_i (after possible " <>
             "solution substitution): "];
      Print[CleanUpFunction[mSoln]];
    ];

    mSoln = 
      mSoln /. 
        {a_List, {(_Rule)..}} :> Sequence[] /;
          Not[ And @@ (FreeQ[ a, #] & /@ myMList  ) ];

    If[systemCleanUpDebug,
      Print["mSoln, after the underdetermined systems are removed: "];
      Print[CleanUpFunction[mSoln]];
    ];

    (* Removes solutions that do not balance at least two independent *)
    (* Terms in the original system. *)
    mSoln =
      mSoln /.
        { {a_List, b : {(_Rule) ..}} :>
            b  /; And @@ ((Length[ Cases[#, Max[#]] ] >= 2)& /@ a),       
          {a_List, b : {(_Rule) ..}} :> 
            Sequence[]
        };

    If[systemCleanUpDebug,
      Print["mSoln, after power balances are checked: "];
      Print[CleanUpFunction[mSoln]];
    ];

    (* Removes solutions with any of the $M_i = 0$. DB:05/25/2003 *)
    mSoln =
      mSoln /.
        a : {(_Rule) ..} :>
          Sequence[] /; Or @@ ( #[[2]] === 0 & /@ a );

    If[systemCleanUpDebug,
      Print["mSoln, after zero solutions are removed: "];
      Print[CleanUpFunction[ mSoln ]];
    ];

    (* Removes negative and rational solutions for the dominate powers. *)
    mSoln =
      mSoln /.
        a : {(_Rule) ..} :>
            Sequence[] /; Or @@
              ( (NonPositive[ #[[2]] ] || ! IntegerQ[ #[[2]] ])& /@ a);
     If[systemCleanUpDebug,
       Print["mSoln, after removing negative and non-integer solutions: "];
       Print[CleanUpFunction[ mSoln ]];
     ];

    (* Removes Tracking Variables. *)
    eqnList = eqnList0 /. myTrackingVariable[_]:>1;

    If[systemCleanUpDebug,
      Print["eqnList, without tracking variables, is: "];
      Print[CleanUpFunction[eqnList]];
    ];

    (* Forms chiList. *)
    eqnList /. \[Chi][i_] :> 
      ( chiList = Append[chiList, \[Chi][i] ]; 1 );
    chiList = Union[chiList];

    If[systemCleanUpDebug,
      Print["chiList, the list of chi's is: "];
      Print[CleanUpFunction[chiList]];
    ];

    (* Finds constraints on chi. *)
    eqnList = 
      MapAll[Factor,
        Plus @@ Coefficient[(eqnList /. #),
                  T^Max[mList /. mSoln]
                ]& /@ mSoln
      ];

    If[systemCleanUpDebug,
      Print["mSoln, checking in eqnList: "];
      Print[CleanUpFunction[eqnList]];
    ];

    (* Returns the good solutions. *)
    Return[mSoln];
  ]; (* end of module mSolve`SystemCleanUp *)

(* Taken from PDESpecialSolutons code on DB:07/23/2004. *)
mSolve`FixFreeM[
    mSoln_List,
    myMList_List,
    opts___?OptionQ
  ] :=
  Module[{ fixFreeMDebug = False, 
           mSoln0,
           mFree, 
           mFreeValues, mFixedValues,
           mValues
         }, (* Protected Local Variables *)
    
    (* Remove symbolic solutions, based on the code in SystemCleanUp. *)
    (* DB:07/29/2004 added removal of rational solutions. *)
    mSoln0 = 
      ( {Rest /@ (# /. Rule -> List), #}& /@ mSoln ) /. 
          {a_List, {(_Rule)..}} :> Sequence[] /;
            Not[ And @@ (FreeQ[ a, #] & /@ myMList  ) ];
    mSoln0 = mSoln0 /. 
      {a_List, {(_Rule)..}} :> Sequence[] /; 
        Not[ And @@ FreeQ[ a, Rational] ];
    mSoln0 = #[[2]]& /@ mSoln0;

    (* Warn the user when potential solutions are removed. *)
    If[Length[Complement[Union[Sort /@ mSoln], mSoln0] ] > 0,
      StylePrint[
        "The potential solutions "<>
        ToString[ 
          InputForm[
            CleanUpFunction[
              Complement[Union[Sort /@ mSoln], mSoln0] 
            ] 
          ]
        ] <> 
        " are being removed because they are underdetermined. ", 
        "Message"
      ];
    ];

    If[fixFreeMDebug,
      Print["mSoln, after the underdetermined systems are removed: "];
      Print[CleanUpFunction[mSoln0]];
    ];

    (* Pick out the solutions with freedom. *)
    mFree = 
      Select[mSoln0, Length[#] < Length[myMList]&];

    If[fixFreeMDebug,
      Print["The dominant behaviors with one or more free \!\(M\_i\): "];
      Print[CleanUpFunction[ mFree ]];
    ];
    (* start if at 111 *)
    If[Length[mFree] >= 1,

      Message[DDESpecialSolutions`dominantBehavior::freevalues,
        CleanUpFunction[ mFree ]
      ];

      (* Substitutes in the values that are fixed, leaving the free values. *)
      mFreeValues = 
        (myMList /. #)& /@ mFree;
      mFixedValues = 
        (myMList /. #)& /@
          Complement[mSoln0, mFree];

      (* DB:02/08/2004 *)
      If[Length[mFixedValues] === 0,
        Message[DDESpecialSolutions`dominantBehavior::underdetermined];
        mFixedValues = 
          mFreeValues /. 
            m[_] :> 0
      ];

      If[fixFreeMDebug,
        Print["The free m values: "];
        Print[CleanUpFunction[ mFreeValues ]];
        Print["The fixed m values: "];
        Print[CleanUpFunction[ mFixedValues ]];
      ];

      mValues = 
        Transpose[
          { #,
            Sequence @@
            Cases[
              mFixedValues,
              # /. (m[i_] :> _)
            ]
          }
        ]& /@ mFreeValues;

      If[fixFreeMDebug,
        Print["The fixed values divided by free values: "];
        Print[CleanUpFunction[ mValues ]];
      ];

      mValues = 
        Sequence @@
          Distribute[
            If[Head[First[#]] === Integer,
              First[#],
              Range[ MinDegreeOfThePolynomial /. {opts} 
                  /. Options[DDESpecialSolutions],
                Max[Rest[#]]
              ]
            ]& /@ #,
            List
          ]& /@ mValues;

      If[fixFreeMDebug,
        Print["Fixing the free values from the " <>
          "MinDegreeOfThePolynomial up to max: "];
        Print[CleanUpFunction[ mValues ]];
      ];

      mValues = 
        ( Rule @@ #& /@ 
          Transpose[
            { myMList,
              #
            }
          ]
        )& /@ mValues;

      If[fixFreeMDebug,
        Print["The fixed values reformatted: "];
        Print[CleanUpFunction[ mValues ]];
      ];

      Return[ mValues ];
    ]; (* closes if at 111 *)
    Return[mSoln0];
  ]; (* end of module mSolve`FixFreeM *)

(* Finds free solutions that result from inequalities. *)
(* Added direct from old code by DB:11/20/2002. *)
mSolve`GenerateAlternativeSolutions[
    mList_List, 
    opts___? OptionQ
  ]:=
  Module[{ n (* The number of alpha[i] *)
         }, (* Protected Local Variables *)
    
    n = Length[ mList ];

    Return[
      Thread[
        mList -> #
      ] & /@ 
        Flatten[
          Outer[
            List,
            Sequence @@ 
              Table[
                Range[ 
                  ( MinDegreeOfThePolynomial /. {opts} /. 
                    Options[DDESpecialSolutions] ),
                  ( MaxDegreeOfThePolynomial  /. {opts} /. 
                    Options[DDESpecialSolutions] )
                ],
                {n}
              ]
          ], 
          n - 1
        ]
    ]
  ]; (* end of module mSolve`GenerateAlternativeSolutions *)

(* ************************************************************************ *)

(* : Title : DDESpecialSolutionsBuildSystem.
*  : Author : Douglas Baldwin
*  : Date : 05-24-01 *)

DDESpecialSolutionsBuildSystem[mSoln_List, system_List, dvars_List, 
    cvars_List,
    param_List, opts___?OptionQ]:=
  Block[{buildSystemDebug = False, (* Debug Boolean. *)
         numberOfEquations,
         uRules,
         tempuRules,
         pureuRules,
         vars,
         newSystem,
         waveparameters,
         unknowns,
         nonzeros,
         maxT,
         time = TimeUsed[],
         myTemp}, (* Protects Local Variables. *)

    (* Sets a local variable to the number of equations given by user. *)
    numberOfEquations = Length[system];

    (* WH:01/23/2009 added tempuRules *)
    (* Converts the results of mSolve to an expression in T *)
    tempuRules = (# /. (m[i_]->j_) -> 
    ( u[i][n][T] -> Evaluate[ Sum[a[i,kk]*T^kk, {kk,0,j}] ]) 
    )& /@ mSoln;

    (* WH:01/23/2009 introduced tempuRules added print statements *)
    (* A list containing both dvars and cvars: *)
    vars = Flatten[{dvars, cvars}];
    If[Verbose /. {opts} /. Options[DDESpecialSolutions],
      Print["Seeking polynomial solutions in T of the form:"];
      Print[CleanUpFunction[tempuRules]];
      Print["where T = Tanh[",
            CleanUpFunction[Sum[c[l]*vars[[l]], {l, Length[vars]}] + phase], 
            "]."]
    ];

    (* Converts the results of mSolve to an expression in T *)
    uRules =  mSoln /. (
      (m[i_]->j_):>
        ( u[i][var__] :> 
          Function[{F}, 
            Sum[
              a[i,k]*
              (
                (F + 
                  Tanh[
                    Sum[Part[{var}-dvars, l]*c[l], 
                      {l, Length[dvars]}
                    ]
                  ]
                )/(
                  1+F*Tanh[
                           Sum[Part[{var}-dvars, l]*c[l], 
                               {l, Length[dvars]}
                               ]
                          ]
                )
              )^k,
              {k,0,j}
            ]
          ]
        )
      );

    If[buildSystemDebug,
      Print["The rules in function format (uRules):"];
      Print[CleanUpFunction[ uRules ]];
    ];

    (* Converts form of solutions given by solver to a pure function. *)
    toPure = 
      (# /. (a__[var__]->temp__) :> (a :> Function[{var}, temp]))&;

(* WH:01/23/2009 added pureuRules to see the format of such rules *)
    pureuRules = toPure[#]& /@ uRules;
    If[buildSystemDebug,
      Print["The rules converted into pure function format (pureuRules): "];
      Print[CleanUpFunction[ pureuRules ]];
    ];

    (* Applies the expressions in T to the system and removes the *)
    (* tracking variables. *)
    newSystem = 
      Expand[
        system //. Append[toPure[#], myTrackingVariable[_]->1]
      ]& /@ uRules;

    If[buildSystemDebug,
      Print["The system after applying the function rules (uRules): "];
      Print[CleanUpFunction[ newSystem ]];
    ];

    (* Clears the denominator to simplify the system. *)
    newSystem = 
      Map[Numerator[Together[#]] &, newSystem, 2];

    If[buildSystemDebug,
      Print["Clearing the denominator yields:"];
      Print[CleanUpFunction[ newSystem ]];
    ];

    (* Prints out warning, if it is taking too long. *)
    If[TimeUsed[]-time > 3,
      Print["Still building the nonlinear algebraic system, please wait."]
    ];

    (* Creates a list with the wave parameters (c[1], c[2]) to be *)
    (* passed to the solver. *)

    waveparameters = 
      Flatten[
        {
          Table[ Tanh[ c[i] ], {i, Length[dvars]} ],
          Table[ c[i], {i, Length[dvars] + 1, Length[dvars] + Length[cvars]}]
        }
      ];

    (* Creates a list of all the a[i,j]'s to be passed to the solver. *)
    unknowns =
      Table[Table[a[i,j], {j, 0, m[i] /. #}], {i, numberOfEquations}]& /@
      mSoln;

    (* Creates a list of those variables which must be nonzero, so as *)
    (* to simplify the work of the solver. *)
    nonzeros = 
      Join[param, 
        Last /@ #, 
        waveparameters
      ]& /@ unknowns;

    (* Flattens the sublists and reorders them to speed up the solver. *)
    unknowns = 
    Map[
        Reverse,
           #[[2]]& /@ #& /@ 
           (Sort[{# /. a_[b_,c_]:>{c,a,b},#}& /@ Flatten[#] ]& /@ unknowns) 
       ];

    (* Expands the system. *)
    newSystem = MapAll[Expand,newSystem];

    (* Determines the maximum exponent of T in each of the cases. *)
    maxT = 
      Map[
        Exponent[#,T]&, 
        newSystem
      ]/. -Infinity -> 0 (* DB:03/21/2003 Infinity rule added. *);

    (* Brakes the expressions up newSystem by powers of T. *)
    newSystem = Table[
      Table[
        (Sort[{Length[#], #}& /@ 
          Union[
            Flatten[
              DeleteCases[
                Flatten[
                  Table[
                    Table[
                      Coefficient[
                        Expand[newSystem[[case,k]] ], 
                        T, 
                        i
                      ], 
                    {i, 0, maxT[[case,j]]}], 
                  {j, numberOfEquations}]
                ], 0
              ]
            ]
          ]
         ] /. {_Integer, a__}:>a
        ), {k, Length[newSystem[[case]] ]}
      ], {case, Length[newSystem]}];

    If[buildSystemDebug,
      Print["After breaking up the system by powers of T, one gets: "];
      Print[CleanUpFunction[ newSystem ]];
    ];

    (* Converts from expressions to equations. *)
    newSystem = 
      DeleteCases[(# == 0)& /@ Flatten[#]& /@ newSystem,
        False || True, Infinity];

    (* DB:10/03/2003 Add expansion for Tanh[c[1] + c[2]]. *)
    (* Moved down in the function on 10/4/2003 *)
    newSystem = 
      newSystem //. 
        Tanh[a_Integer*c[b_Integer] + d__] :> 
          ((Tanh[a*c[b]] + Tanh[d])/(1 + Tanh[a*c[b]]*Tanh[d]));

    If[buildSystemDebug,
      Print["After expanding Tanh[c[i] + c[j]], one gets: "];
      Print[CleanUpFunction[ newSystem ]];
    ];

    newSystem = 
      Map[Numerator[Together[#]] &, newSystem, 3];

    If[buildSystemDebug,
      Print["Clearing the denominator: "];
      Print[CleanUpFunction[ newSystem ]];
    ];
    
    (* DB:01/21/2003, Strips the non-zeros at this step. *)
    newSystem = 
      MapThread[StripNonZero, 
        { newSystem, 
          Flatten[{#, Tanh[_Integer*c[_]] } ]& /@ nonzeros
        }
      ];

    If[buildSystemDebug,
      Print["After getting rid of non-zeros, one gets: "];
      Print[CleanUpFunction[ newSystem ]];
    ];

    (* Formats the system so it can be read by analyze and solve. *)
    newSystem = 
     MapAll[Factor, 
       Transpose[
         { newSystem, 
            unknowns, 
            Table[waveparameters, {Length[newSystem]}],
            Table[param, {Length[newSystem]}],
            nonzeros
         }
       ]
     ];

    If[buildSystemDebug,
      Print["The system formatted for solving by AnalyzeAndSolve routine: "];
      Print[CleanUpFunction[ newSystem ]];
    ];

    (* DB:03/21/2003 remove inconsistent systems. *)
    (* Modified DB:09/30/2003 *)
    newSystem = 
      newSystem /. 
        { {{___, False, ___}, __} :> Sequence[], 
          {{}, __} :> Sequence[]
        };

    If[buildSystemDebug,
      Print["Removing inconsistent systems yields: "];
      Print[CleanUpFunction[ newSystem ]];
    ];

    (* If there are no systems to be solved, then abort. *)
    (* DB:03/21/2003 *)
    If[Length[newSystem] === 0,
      Message[ DDESpecialSolutionsBuildSystem::fail ];
      Abort[ ]
    ];

    (* Combines into lists containing {newSystem, unknowns, *)
    (* waveparameters, param, nonzeros} for the solver. *)
    Return[
      newSystem
    ]
  ]; (* end of block DDESpecialSolutionsBuildSystem *)

(* ************************************************************************ *)

(* : Title : StripNonZero *)
(* : Author : Douglas Baldwin *)
(* : Summary : Strips parameters from expressions. *)

StripNonZero[{a : (_List) ..}, param_List] := 
  StripNonZero[#, param] & /@ {a};

StripNonZero[theList_List, param_List] :=
    Module[
      {result, stripDebug = False}, (* Local Variables *)
     
      If[stripDebug,
        Print["The original expression: "];
        Print[CleanUpFunction[ MapAll[Factor, theList] ]];
      ];

      (* Maps factor to every term, so as to have a constant base. *)
      result =  FactorList /@ (theList /. Equal[a_,b_]:>a-b);
      
      If[stripDebug,
        Print["The result after applying FactorList: "];
        Print[CleanUpFunction[ result ]];
      ];
      
      If[stripDebug,
        Print["The rules are: "];
        Print[
          CleanUpFunction[ 
            {({#^_:1, _} :> Sequence[] & /@ param), 
             {_?NumericQ, _} :> Sequence[]
            } ]
        ];
      ];

      (* Remove terms that are non-zero. *)
      result = result /. ({#^_:1, _} :> Sequence[] & /@ param);
      (* DB:10/02/2003 - Removes Tanh[j*c[i]] *)
      result = result /. ({Tanh[_ * c[_]]^_ : 1, _} :> Sequence[]);

      (* Remove terms that are numeric. *)
      result = result /. {_?NumericQ, _} :> Sequence[];

      If[stripDebug,
        Print["The result after applying the non-zero rules: "];
        Print[CleanUpFunction[ result ]];
      ];
      
      (* Puts it back into standard form, {a, b} to a*b *)
      result = Times @@ (First[#]^Last[#]&) /@ #& /@ result;

      If[stripDebug,
        Print["Converting back to the standard form: "];
        Print[CleanUpFunction[ result ]];
      ];

      (* Converts expressions back into equations. *)
      If[! FreeQ[theList, Equal],
        result = Equal[#,0]& /@ result;
        ];

      If[stripDebug,
        Print["The final result after stripping the non-zeros: "];
        Print[CleanUpFunction[ result ]];
      ];
      Return[ result ];
      ]; (* end of module StripNonZero *)

(* ************************************************************************ *)

(* : Title : DDESpecialSolutionsBuildSolutions *)
(* : Author : Douglas Baldwin *)
(* : Summary : Builds (includes massive simplification) *)
(*   and, if requested, also tests the final solutions. *)

DDESpecialSolutionsBuildSolutions[solution_, mSoln_, 
   eqns_, funcs_, dvars_, cvars_, param_, opts___] :=
   Block[{buildSolnDebug = False, (* Debug Boolean *)
         solutionRules, (* Local version of solution*)
         vars, (* dvars and cvars. *)
         MySimplificationRules, (* Simplification rules *)
         VerboseTest = Verbose /. {opts} /. Options[DDESpecialSolutions],
         numericTestSolutions, (* numeric test solns *)
         symbolicTestSolutions, (* symbolic test solutions *)
         (* tempSymbolicTestSolutions, (* symbolic test solutions *) *)
         soln = {}, (* Holds the solutions. *)
         tempsoln, (* Temporarily holds the solutions *)
         lensoln, (* length of soln *)
         lentempsoln, (* length of tempsoln *)
         difflensoln, (* difference of lensoln and lentempsoln *)
         time = TimeUsed[], (* Time tester. *)
         warn = {} (* Collects a list of warning from simplifying *)
        }, (* Protected Local Variables. *)

    (* Sets up a local version to modify *)
    solutionRules = MapAll[Factor, solution]; 

    (* A list containing both dvars and cvars: *)
    vars = Flatten[{dvars, cvars}];

    If[buildSolnDebug,
      Print["The variables (vars) are: "];
      Print[CleanUpFunction[ vars ]];
    ];

    (* Builds the solutions from the above rules and *)
    (* the powers of T listed in the passed mSoln. *)

(* WH: 03/17/2010 debugging, can be commented out after debugging *)
(*
    solutionRuleswithoutDeleteCases = 
          Table[
            Table[
              Join[(mSoln[[jj]] /. (m[i_]->j_):>
                (funcs[[i]][ Sequence @@ vars ] -> 
                  Sum[
                    a[i,k]* 
                      Tanh[ Sum[c[l]*vars[[l]], {l, Length[vars]}]+phase]^k, 
                    {k, 0, j}
                  ]
                )) //. 
                    solutionRules[[jj, ii]],
                (# -> (# /. solutionRules[[jj,ii]]))& /@ param
              ],
              {ii, Length[solutionRules[[jj]]]}],
          {jj, Length[mSoln]} 
          ]; (* end table *)
*)

(*
Print["At Pt. L1, before DeleteCases, solutionRuleswithoutDeleteCases :"];
Print[CleanUpFunction[solutionRuleswithoutDeleteCases]];
Print["At Pt. L2, apply CleanUpFunction to solutionRuleswithoutDeleteCases:"];
Print[CleanUpFunction[#]]& /@ solutionRuleswithoutDeleteCases;
*)

(*
    solutionRulesafterfirstDeleteCases = 
        DeleteCases[
          Table[
            Table[
              Join[(mSoln[[jj]] /. (m[i_]->j_):>
                (funcs[[i]][ Sequence @@ vars ] -> 
                  Sum[
                    a[i,k]* 
                      Tanh[ Sum[c[l]*vars[[l]], {l, Length[vars]}]+phase]^k, 
                    {k, 0, j}
                  ]
                )) //. 
                    solutionRules[[jj, ii]],
                (# -> (# /. solutionRules[[jj,ii]]))& /@ param
              ],
              {ii, Length[solutionRules[[jj]]]}],
          {jj, Length[mSoln]}],
          max[_]->_,
          Infinity
        ];
*)

(*
Print["At Pt. L3, after 1st DeleteCases, solutionRulesafterfirstDeleteCases:"];
Print[CleanUpFunction[solutionRulesafterfirstDeleteCases]];
Print["At Pt. L4, apply CleanUp to solutionRulesafterfirstDeleteCases:"];
Print[CleanUpFunction[#]]& /@ solutionRulesafterfirstDeleteCases;
*)

    solutionRules = 
      DeleteCases[
        DeleteCases[
          Table[
            Table[
              Join[(mSoln[[jj]] /. (m[i_]->j_):>
                (funcs[[i]][ Sequence @@ vars ] -> 
                  Sum[
                    a[i,k]* 
                      Tanh[ Sum[c[l]*vars[[l]], {l, Length[vars]}]+phase]^k, 
                    {k, 0, j}
                  ]
                )) //. 
                    solutionRules[[jj, ii]],
                (# -> (# /. solutionRules[[jj,ii]]))& /@ param
              ],
              {ii, Length[solutionRules[[jj]]]}],
          {jj, Length[mSoln]}],
          max[_]->_,
          Infinity
        ],
        Rule[a_,b_] /; a == b && FreeQ[a, Alternatives @@ funcs],
        Infinity
      ];

(*
Print["At Pt. L5, after second DeleteCases, solutionRules :"];
Print[CleanUpFunction[solutionRules]];
Print["At Pt. L6, apply CleanUpFunction to solutionRules :"];
Print[CleanUpFunction[#]]& /@ solutionRules;
*)

    If[buildSolnDebug,
      Print["The solution rules are: "];
      Print[CleanUpFunction[ solutionRules ]];
    ];

    (* Simplification Rules for reducing the solution *)
    (* even further... so as to find more general solutions. *)
    MySimplificationRules = 
      { Sqrt[xxx__^2] :> 
          (warn = Append[warn, "Sqrt[a^2]->a"]; xxx), 
        Sqrt[Power[yyy__,2]] :> 
          (warn = Append[warn, "Sqrt[a^2]->a"]; yyy), 
        Sqrt[-zzz__^2] :> 
          (warn = Append[warn, "Sqrt[-a^2]->I*a"]; I*zzz),
        Sqrt[-ttt_*zzz__^2] :> 
          (warn = Append[warn, "Sqrt[-a*b^2]->I*b*Sqrt[a]"]; 
          I*zzz*Sqrt[ttt]), 
        Sqrt[-Sech[xx_]^2] :> 
          (warn = Append[warn, "Sqrt[-a^2]->I*a"]; I*Sech[xx]), 
        aaa_/Sqrt[-Sech[xx_]^2] :> 
          (warn = Append[warn, "a/Sqrt[-Sech[x]^2]->-I*a*Cosh[x]"];
           -I*aaa*Cosh[xx]
          ),
        Sqrt[Cosh[xx_]^2] :> 
          (warn = Append[warn, "Sqrt[Cosh[x]^2]->Cosh[x]"]; Cosh[xx]), 
        Sqrt[-Cosh[xx_]^2] :> 
          (warn = Append[warn, "Sqrt[-Cosh[x]^2]->I*Cosh[x]"]; I*Cosh[xx]), 
        aaa_/Sqrt[-Cosh[xx_]^2] :> 
          (warn = Append[warn, "a/Sqrt[-Cosh[x]^2]-> -I*a*(1/Cosh[x])"];
           -I*aaa*(1/Cosh[xx])
          ),
        aaa_/Sqrt[Cosh[xx_]^2] :> 
          (warn = Append[warn, "a/Sqrt[Cosh[x]^2]->-a/Cosh[x]"];
           aaa/Cosh[xx]
          ),
        (1-Sech[xx__]^2) -> Tanh[xx]^2,
        (1-Tanh[xx__]^2) -> Sech[xx]^2,
        (1+Sinh[xx__]^2) -> Cosh[xx]^2,
        (1-Cosh[xx__]^2) -> Sinh[xx]^2
      };  
 
    (* Applies the above rules to the solutions. *)
    (* Changed Simplify to Expand. DB:10/21/2003 *)
    solutionRules = 
      FixedPoint[
        MapAll[Factor,
          MapAll[Expand, 
            # //. MySimplificationRules
          ] //. MySimplificationRules
        ]&,
        solutionRules,
        4
      ];

(* WH:03/17/2010 debugging, can be commented out after debugging *)
(*
Print["At Pt. L7, after applying MySimplificationRules, solutionRules :"];
Print[CleanUpFunction[solutionRules]];
Print["At Pt. L8, apply CleanUpFunction to solutionRules :"];
Print[CleanUpFunction[#]]& /@ solutionRules;
*)

    (* Removed repeated solutions. DB:10/21/2003 *)
    solutionRules = 
      Union /@ solutionRules;

(*
Print["At Pt. L9, after Union, solutionRules :"];
Print[CleanUpFunction[solutionRules]];
Print["At Pt. L10, apply CleanUpFunction to solutionRules :"];
Print[CleanUpFunction[#]]& /@ solutionRules;
*)

    (* Prints out a warning, if things are taking too long. *)
    If[TimeUsed[] - time > 3,
      Print["Still building the solutions, please wait."]
    ];
    (* Depending on the test option, we either proceed with *)
    (* testing of solutions, or we don't. *)
    (* start if 00 *)
    If[ ( !(NumericTest /. {opts} /. Options[DDESpecialSolutions]) && 
          !(SymbolicTest /. {opts} /. Options[DDESpecialSolutions]) ),
      CellPrint[
        Cell[
        "These solutions are not being tested numerically or symbolically",
        "Message"
        ]
      ];
      CellPrint[
        Cell[
        "To test the solutions set either the NumericTest option to True ", 
        "Message"
        ]
      ];
      CellPrint[
        Cell[
        "or set the SymbolicTest option to True, or both. ", 
        "Message"
        ]
      ];

      (* WH:03/17/2010 formatted the cellprint lines were too long, *)
      (* or print too small in Mathematica v. 7.0 *)
      If[Length[warn]>0,
        CellPrint[
          Cell[
          "The following simplification rules are being used:",
          "Message"
          ] 
        ];
        CellPrint[
          Cell[
          ToString[Union[warn]],
          "Message"
          ] 
        ];
      ]; (* end if *)
      Return[
        Map[Union,
          MapAll[Factor,
            MapAll[Expand,
              solutionRules
            ]
          ], 2
        ]
      ]
    ]; (* end if 00 *)

    (* Prints the untested solutions to the user. *)
    If[VerboseTest,
      Print["The possible non-trivial solutions (before any testing): "];
      Print[CleanUpFunction[solutionRules]]
    ];

    (* Converts to a pure function. *)
    toPure = 
      (# /. (a__[var__]->temp__):> (a:>Function[{var}, temp]))&;

    (* WH:03/17/2010 always print the message about numerically testing *)
    (* start If statement for the numerically test option. *)
    If[NumericTest /. {opts} /. Options[DDESpecialSolutions],
      (* Sends message to user. *)
      If[(Verbose /. {opts} /. Options[DDESpecialSolutions]),
        Print["Numerically testing the solutions."]
      ];

    (* WH:03/17/2010 Added a print statement *)
    If[VerboseTest,
       Print["The following solutions will be numerically tested:"];
       Print[CleanUpFunction[solutionRules]]
       ];

(* WH:03/17/2010 testing what happens to solutions that do not work. *)
(* Change the lists solns and solutionRules artifically to test *)
(* if complement works *)

(* solns = solns /. { 15 -> N[Pi,4] }; *)

(* 
Print["At Pt. R3-tris, solns in RAW form: "];
Print[solns];
*)

(* 
Print["At Pt. R3-quatro (after HACK), solns: "];
Print[CleanUpFunction[solns]];
Print["length of solns (after HACK):", Length[solns[[1]]]];
*)

(* solutionRules1 = solutionRules[[1]][[1]] /. { Sinh[c[1]] -> Cosh[c[1]] }; *)

(*
Print["At Pt. R3-4a (after HACK), solutionRules1: "];
Print[CleanUpFunction[solutionRules1]];
*)

(*
solutionRules2 = solutionRules[[1]][[2]]; 
*)

(*
Print["At Pt. R3-4b (after HACK), solutionRules2: "];
Print[CleanUpFunction[solutionRules2]];
*)

(*
solutionRules = {{solutionRules1, solutionRules2}}; 
*)

(* 
Print["At Pt. R3-5, solutionRules in RAW form: "];
Print[solutionRules];
*)

(* 
Print["At Pt. R3-6 (after HACK), solutionRules: "];
Print[CleanUpFunction[solutionRules]];
Print["length of solutionRules (after HACK):", Length[solutionRules[[1]]]];
*)

      (* Tests to make sure the above solutions are valid. *)
      (* Changed toPure[MapAll[TrigToExp, #]] DB:10/21/2003 *)
      numericTestSolutions =
        {(eqns /. (a__==b__):>(a-b)) //. toPure[#], #}& /@ 
          #& /@ solutionRules;

      If[buildSolnDebug,
        Print["The system after substituting the solutions: "];
        Print[CleanUpFunction[ numericTestSolutions ]];
      ];

      randomVarRules = 
        Append[
          (# -> Random[Real, {-1, 1}])& /@ 
            Join[vars, Array[c, Length[vars]]],
          phase -> 0
        ];

      randomAijRules = 
        { a[_,_]->Random[Real, {-1, 1}], 
          Sequence @@ ((# -> Random[Real, {-1, 1}])& /@ param )
        };

      (* Numerically testing the solutions by replacing all the symbols with *)
      (* random numbers. *)
      numericTestSolutions = 
       { Or[
           And @@
           (
             Abs[ # ] < 10^(-$MachinePrecision/2)& /@ 
               ( MapAll[ Expand,
                   #[[1]] /. randomVarRules
                 ] /. 
                 randomAijRules 
               )
           ),
           And @@
           (
             Abs[ # ]  < 10^(-$MachinePrecision/2)& /@ 
               ( MapAll[ Expand,
                   #[[1]] /. ( randomVarRules /. (a_ -> b_) :> (a -> -b) )
                 ] /. 
                 ( randomAijRules /. (a_ -> b_) :> (a -> -b) )
               )
           )
         ],
         #
       }& /@ #& /@ numericTestSolutions;

(* WH:03/17/2010 for debugging only *)
(*
Print["At Pt. K1, list of numericTestSolutions:"];
Print[CleanUpFunction[numericTestSolutions]];
Print["At Pt. K2, apply CleanUpFunction to list of numericTestSolutions:"];
Print[CleanUpFunction[#]]& /@ numericTestSolutions;
*)

      (* If it works for any of the trials, it keeps the solution. *)
      soln = 
        numericTestSolutions /. { {True, a_} :> a[[2]], 
                                  {False, _} :> Sequence[] };

(*
Print["At Pt. K3, list of soln:"];
Print[CleanUpFunction[soln]];
Print["At Pt. K4, apply CleanUpFunction to list of soln:"];
Print[CleanUpFunction[#]]& /@ soln;
Print["The above soln is the list of solutions that PASSED the NUMERIC test."];
*)

    (* WH:03/17/2010 added a print statement *)
    If[VerboseTest,
       Print["The following solutions passed the numerical test:"];
       Print[CleanUpFunction[soln]]
       ];

(*
      If[buildSolnDebug,
        Print["The numerically tested solutions are: "];
        Print[CleanUpFunction[ soln ]];
      ];
*)

(* WH: 03/17/2010 the complement below malfunctioned *)
(* Baldwin's code was *)
(*
      numericTestSolutions = 
        Complement[solutionRules, soln];
*)
(* WH: 03/17/2010 replaced by *)

   numericTestSolutions = 
        { Complement[ solutionRules[[1]], soln[[1]] ] };

(*
Print["At Pt. K4-bis, list of solutionRules:"];
Print[CleanUpFunction[solutionRules]];
Print["At Pt. K4-tris, list of soln:"];
Print[CleanUpFunction[soln]];

Print["At Pt. K5, list of numericTestSolutions (which is "<>
      "the complement of solutionRules and soln):"];
Print[CleanUpFunction[numericTestSolutions]];
Print["At Pt. K6, apply CleanUpFunction to list numericTestSolutions:"];
Print[CleanUpFunction[#]]& /@  numericTestSolutions;
Print["The above numericTestSolutions is the list of solutions that DID NOT "<>
      "pass the NUMERIC test."];
*)

      (* WH:03/17/2010 formatted the cellprint lines were too long, *)
      (* or print too small in Mathematica v. 7.0 *)
      (* start if 11 *)
      If[(numericTestSolutions //.  {{}}->{}) != {},
        CellPrint[
          Cell[
          "After subsitution of the solutions into the DDE, the resulting "<>
          "expressions did not simplify to be less than 10^(" <>
          ToString[-$MachinePrecision/2] <>
          ") ",
          "Message"
          ]
        ];
        CellPrint[
          Cell[
          "when random numbers in [-1,1] were substituted for the " <>
          "unknowns.  " <>
          "This could be caused from Mathematica's assumption that " <>
          "Sqrt[a^2] -> a when a is numeric.  ",
          "Message"
          ]
        ];
(* 
        CellPrint[
          Cell[
          "Please test the corresponding solutions by hand or interactively "<>
          "with Mathematica.",
          "Message"
          ]
        ]; 
*)
        Print[CleanUpFunction[#]]& 
          /@ numericTestSolutions;
        CellPrint[ 
          Cell["Please test these solutions by hand or interactively with "<>
          "Mathematica.",
          "Message"
          ]
        ];
      ]; (* end if 11 *)
    ]; (* end of numeric test if statement. *)

    (* The symbolic test if statement. *)
    (* If statement for the symbolic test option. *)
    (* WH:03/17/2010 always print the message about symbolic testing *)
    (* start of symbolic test If statement. *)
    If[SymbolicTest /. {opts} /. Options[DDESpecialSolutions],
      (* Sends message to user. *)
       If[(Verbose /. {opts} /. Options[DDESpecialSolutions]),
         Print["Symbolically testing the solutions."];
         Print["WARNING: the symbolic test of solutions may be slow."];
         Print["Be patient! To skip the symbolic test, set the option "<>
                "SymbolicTest to False."]
       ];

(* WH:03/17/2010 added a line of code and a print statement. *)
(* Under the default setting, soln would come out of the numeric test. *)
(* therefore, the soln would be {} if numeric test is set to False. *)
(* So, if numeric test is false, set soln = solutionRules, but simplify *)
(* solutionRules a bit *)

       If[!(NumericTest /. {opts} /. Options[DDESpecialSolutions]), 
           soln = ( ( solutionRules 
           ) /. (p_ -> q_) :> (p -> Expand[q])
           ) /. (p_ -> q_) :> (p -> Factor[q])
       ];

(* WH:03/17/2010 only test solutions (soln) that passed the numeric test. *)
(* Added a print statement to specify which solutions are being tested. *)
      If[VerboseTest,
         If[(NumericTest /. {opts} /. Options[DDESpecialSolutions]), 
           Print["Only the solutions that passed the numeric test will "<>
           "be tested symbolically."];
           Print["To test all solutions, set the option NumericTest to False."]
        ]
      ];
      If[VerboseTest,
         Print["The following solutions will be tested symbolically:"];
         Print[CleanUpFunction[soln]]
        ];

(* WH:03/17/2010 count the number of solutions to be tested *)
(* account for lists like { { {1st sol},{2nd sol} }, {{3rd sol, cond.}} } *)
   If[Length[soln] === 1, 
       lensoln = Length[ soln[[1]] ], (* else *) 
       lensoln = 
         Table[ Length[ soln[[kk]] ], {kk,1,Length[soln]} ] /. List -> Plus
   ];

(*
Print["At Pt. K7-a, number of solutions to be tested, lensoln:"];
Print[CleanUpFunction[lensoln]];
*)
(* Print["Time Used:", TimeUsed[]-time]; *)

      (* This sets up the input for the next block of code. *)
      (* In that case, it takes the equations given by the user, *)
      (* and replaces the user defined functions (e.g. u[n,t]) *)
      (* with the functions found within the algorithm.  To replace *)
      (* the partial derivatives correctly, we must first convert *)
      (* the solutions to pure functions. *)

(* WH:03/17/2010 added the following code to speed things up *)
(* also replaced solutionRules by soln, set phase  = 0 *)

(*      tempSymbolicTestSolutions = *)
        symbolicTestSolutions =
        { (eqns /. a__ == b__ :> a-b) /. 
          toPure[(# /. (p_ -> q_) :> (p -> TrigToExp[q]))], # }& /@ 
          #& /@ (soln /. {phase -> 0});

(* 
Print["At Pt. K7-b, NEW CODE, list of tempSymbolicTestSolutions:"];
Print[CleanUpFunction[tempSymbolicTestSolutions]];
Print["Time Used:", TimeUsed[]-time];
*)

symbolicTestSolutions = MapAll[Factor, symbolicTestSolutions];

(* tempSymbolicTestSolutions = MapAll[Factor, tempSymbolicTestSolutions]; *)
(*
Print["At Pt. K7-c, after MapAll Factor, list of tempSymbolicTestSolutions:"];
Print[CleanUpFunction[tempSymbolicTestSolutions]];
Print["Time Used:", TimeUsed[]-time];
*)

symbolicTestSolutions = MapAll[Factor, symbolicTestSolutions];
(* tempSymbolicTestSolutions = MapAll[Factor, tempSymbolicTestSolutions]; *)
(*
Print["At Pt. K7-d, apply MapAll Factor 2nd time, tempSymbolicTestSolutions:"];
Print[CleanUpFunction[tempSymbolicTestSolutions]];
Print["Time Used:", TimeUsed[]-time];
*)

(* WH:03/17/2010 only test solutions (soln) that passed the numeric test. *)
(* If the numeric test was skipped then soln = solutionRules *)
(* WH:03/17/2010 replaced solutionRules by soln *)
(* Baldwin's code:
      symbolicTestSolutions = 
        { DDESpecialSolutionsBuildSolutions`mySimplify[
            TrigToExp[(eqns /. (a__==b__) :> (a-b)) //. toPure[#]]
          ], #
        }& /@ #& /@ (* solutionRules *) soln;
*)

(* WH:03/17/2010 replaced by *)
(* First, collect the solutions that already tested to be correct *)

      (* Pulls off the solutions which simplify to zero *)
      tempsoln = 
          { Cases[symbolicTestSolutions /. {{a__}} :> {a},
            {{(0)..}, _List},
            Infinity
          ] //. {{(0)..}, a_List} :> a
          }; (* DB:08/02/2003 changed :>{a} to {...:>a} *)

(*
Print["At Pt. K7-e, pick out solutions that are correct, list tempsoln:"];
Print[CleanUpFunction[tempsoln]];
Print["Time Used:", TimeUsed[]-time];
*)

(* WH:03/17/2010 count the number of correct solutions *)
(* here we do not have to account for lists like *)
(* { { {1st sol},{2nd sol} }, {{3rd sol, cond.}} } *)

lentempsoln = Length[ tempsoln[[1]] ]; 

(*    If[Length[tempsoln] === 1, 
       lentempsoln = Length[ tempsoln[[1]] ], (* else *) 
       lentempsoln = 
         Table[ Length[ tempsoln[[kk]] ], {kk,1,Length[tempsoln]} ] /. 
         List -> Plus
   ]; 
*)

(*
Print["At Pt. K7-f, number of solutions that are correct, lentempsoln:"];
Print[CleanUpFunction[lentempsoln]];
(* Print["Time Used:", TimeUsed[]-time]; *)
*)

difflensoln = lensoln-lentempsoln;

(*
Print["At Pt. K7-g, number of solutions that are not correct, difflensoln:"];
Print[CleanUpFunction[difflensoln]];
(* Print["Time Used:", TimeUsed[]-time]; *)
*)

(* WH:03/17/2010 only call on mySimplify code after two MapAll Factor failed *)
(* Print statements added *)
(* start if difflensoln not zero *)
If[difflensoln =!= 0, (* then *)
  If[buildSolnDebug,  
     Print["Calling on extra simplications (mySimplify subroutine)"]
  ];
      symbolicTestSolutions = 
        { DDESpecialSolutionsBuildSolutions`mySimplify[
            TrigToExp[(eqns /. (a__==b__) :> (a-b)) //. toPure[#]]
          ], #
        }& /@ #& /@ soln;
  If[buildSolnDebug,
        Print["The expression after trying to simplify the solutions: "];
        Print["using code DDESpecialSolutionsBuildSolutions`mySimplify"];
        Print[CleanUpFunction[symbolicTestSolutions]];
        Print["Time Used:", TimeUsed[]-time]
  ], (* else *) 
  If[buildSolnDebug,
        Print["The expression after trying to simplify the solutions: "];
        Print["NOT using code DDESpecialSolutionsBuildSolutions`mySimplify"];
        Print[CleanUpFunction[symbolicTestSolutions]];
        Print["Time Used:", TimeUsed[]-time]
  ]
]; (* end if difflensoln not zero *)

(*
      If[buildSolnDebug,
        Print["The expression after trying to simplify the solutions: "];
        Print["using code DDESpecialSolutionsBuildSolutions`mySimplify"];
        Print[CleanUpFunction[symbolicTestSolutions]];
        Print["Time Used:", TimeUsed[]-time]
      ];
*)

(* WH:03/17/2010 do no longer join the original (not-tested) and the tested *)
(* solutions. Replace the following: *)

(*
      (* Pulls off the solutions which simplify to zero, and adds *)
      (* them to soln (the final output applies an union), so *)
      (* duplicate solutions are not an issue at this point. *)
      soln = 
        Join[soln,
          { Cases[symbolicTestSolutions /. {{a__}} :> {a},
              {{(0)..}, _List},
              Infinity
            ] //. {{(0)..}, a_List}:>a 
          } (* DB:08/02/2003 changed :>{a} to {...:>a} *)
        ]; (* end join *)

      If[buildSolnDebug,
        Print["The symbolically tested solutions (joined with the " <>
              "numerically tested solutions): "];
        Print[CleanUpFunction[ soln ]];
      ];
*)

(* WH:03/17/2010 replaced the above code by the following code (below) *)
(* 
Print["At Pt. K7, list of symbolicTestSolutions:"];
Print[CleanUpFunction[symbolicTestSolutions]];
Print["At Pt. K8, apply CleanUpFunction to list of symbolicTestSolutions:"];
Print[CleanUpFunction[#]]& /@ symbolicTestSolutions;
*)

      (* Pulls off the solutions which simplify to zero *)
      soln = 
          { Cases[symbolicTestSolutions /. {{a__}} :> {a},
            {{(0)..}, _List},
            Infinity
          ] //. {{(0)..}, a_List} :> a
          }; (* DB:08/02/2003 changed :>{a} to {...:>a} *)

(* 
Print["At Pt. K9, list of soln:"];
Print[CleanUpFunction[soln]];
Print["At Pt. K10, apply CleanUpFunction to list of soln:"];
Print[CleanUpFunction[#]]& /@ soln;
Print["The above soln is list of solutions that PASSED the SYMBOLIC test."];
*)

    If[VerboseTest,
       Print["The following solutions (in factored form) passed "<>
             "the symbolic test:"];
       Print[CleanUpFunction[soln]]
       ];

      (* Removes all the good cases, so we may output the bad cases *)
      (* to the user.*)
      symbolicTestSolutions = 
        DeleteCases[
          DeleteCases[symbolicTestSolutions,
            {{(0)..}, _List},
            Infinity
         ],
         {}
       ];

(* 
Print["At Pt. K11, list of symbolicTestSolutions:"];
Print[CleanUpFunction[symbolicTestSolutions]];
Print["At Pt. K12, apply CleanUpFunction to list symbolicTestSolutions:"];
Print[CleanUpFunction[#]]& /@ symbolicTestSolutions;
Print["The above symbolicTestSolutions is list of solutions that DID NOT "<>
      "pass the SYMBOLIC test."];
*)

      (* WH:03/17/2010 formatted the cellprint lines were too long, *)
      (* or print too small in Mathematica v. 7.0 *)
      If[(Map[Union, symbolicTestSolutions, 3] //. {{}}->{}) != {},
        (* Sends the left over (questionable) solutions to *)
        (* the user for interactive inspection *)
        CellPrint[
          Cell[
            "The following results did not easily simplify to zero. ",
            "Message"
          ]
       ];
        CellPrint[
          Cell[
            "Please test these solutions by hand or interactively with " <>
            "Mathematica: ",
            "Message"
          ]
       ];
       Print[CleanUpFunction[#]]& /@ symbolicTestSolutions;
     ];
   ]; (* end of symbolic test if statement *)

      (* Prints simplification rules to the screen *)
      (* WH:03/17/2010 formatted the cellprint lines were too long, *)
      (* or print too small in Mathematica v. 7.0 *)
      If[Length[warn]>0,
        CellPrint[
          Cell[
          "The following simplification rules are being used:",
          "Message"
          ] 
        ];
        CellPrint[
          Cell[
          ToString[Union[warn]],
          "Message"
          ] 
        ];
      ]; (* end if *)
   (* Returns the solution rules *)
   Return[
     Union[
       MapAll[Factor,
         MapAll[Expand,
           soln
         ]
       ]
     ]
   ]; 
 ]; (* end of block DDESpecialSolutionsBuildSolutions *)

(* mySimplify routine used in symbolic test *)

DDESpecialSolutionsBuildSolutions`mySimplify[expr_List] :=
  DDESpecialSolutionsBuildSolutions`mySimplify /@ expr;

DDESpecialSolutionsBuildSolutions`mySimplify[0, _] := 0;

(* WH:03/17/2010 four tests is probably too many, makes testing too slow! *)
(* 
DDESpecialSolutionsBuildSolutions`mySimplify[expr_, i_Integer:0] :=
  DDESpecialSolutionsBuildSolutions`mySimplify[ MapAll[Factor,expr], i+1] /;
    EvenQ[i] && i < 7;
*)
(* replaced by maximum of three tests: i=0, i=1, and i=2 *)
DDESpecialSolutionsBuildSolutions`mySimplify[expr_, i_Integer:0] :=
  DDESpecialSolutionsBuildSolutions`mySimplify[ MapAll[Factor,expr], i+1] /;
    EvenQ[i] && i < 3;

(* WH:03/17/2010 six tests is probably too many, makes testing too slow *)
(* 
DDESpecialSolutionsBuildSolutions`mySimplify[expr_, i_Integer] :=
  DDESpecialSolutionsBuildSolutions`mySimplify[ Expand[expr], i+1] /;
    OddQ[i] && i < 6;
*)
(* replaced by maximum of three tests  *)
DDESpecialSolutionsBuildSolutions`mySimplify[expr_, i_Integer] :=
  DDESpecialSolutionsBuildSolutions`mySimplify[ Expand[expr], i+1] /;
    OddQ[i] && i < 2;
(*
DDESpecialSolutionsBuildSolutions`mySimplify[expr_, i_ /; i >= 7] := expr;
(* replaced by *)
*)
DDESpecialSolutionsBuildSolutions`mySimplify[expr_, i_ /; i >= 3] := expr;
  
(* ************************************************************************ *)

(* : Title : CleanUpFunction *)
(* : Author : Douglas Baldwin *)
(* : Summary : Remove "DDESpecialSolutionsPrivate`" from output. *)

CleanUpFunction = 
   ToExpression[
     StringReplace[ToString[InputForm[#]],
       "Calculus`DDESpecialSolutions`Private`"->""
     ]
   ]&

End[] (* `Private` context *)

SetAttributes[DDESpecialSolutions, ReadProtected]

EndPackage[]

(* START OLD ANALYZESOLVE OF 2003 OLD 

(* ************************************************************************ *)

(* Nonlinear algebraic solver of Unal Goktas (WRI) and Willy Hereman *)
(* Written by Unal Goktas in October/November 2000 *)
(* Comments added by Douglas Baldwin on Monday, January 13, 2003 *)
(* DB:01/13/2003. Reverted back to Non-HighestOrder code DB:02/02/2003 *)

BeginPackage["Algebra`AnalyzeAndSolve`"]

Unprotect[AnalyzeAndSolve]

AnalyzeAndSolve::soln = 
"The solution `1` is being removed because it is inconsistent."

Begin["`Private`"]

If[$VersionNumber < 4,
   Attributes[Internal`DeactivateMessages] = {HoldAll};
   Internal`DeactivateMessages[body_, msgs___MessageName] :=
      Module[{wasOn = Select[Hold[msgs], Head[#] =!= $Off &], result},
         CheckAbort[
            Scan[Off, wasOn];
            result = body;
            Scan[On, wasOn];
            result,
            Scan[On, wasOn];
            Abort[]
         ]
      ] (* end of module Internal`DeactivateMessages *)
]; (* end if VersionNumber < 4 *)

If[$VersionNumber >= 5,
   Developer`SetSystemOptions[
      "ReduceOptions" -> {"ReorderVariables" -> False}
   ];
   myReduce[eqn_, vars_] := 
    ( If[Verbose /. Options[DDESpecialSolutions], 
        Print[CleanUpFunction[#]]
        ];
      #)&[
      LogicalExpand[
        Reduce[eqn, Reverse[vars]] /. Equal -> myEqual
    ] /. myEqual -> Equal],
   myReduce[eqn_, vars_] := 
    (If[Verbose /. Options[DDESpecialSolutions], 
        Print[CleanUpFunction[#]]
        ];
      #)&[
      Reduce[eqn, vars, Sort -> False]
    ]
]; (* end if VersionNumber >= 5 *)

(* : Title : CleanUpFunction *)
(* : Author : Douglas Baldwin *)
(* : Summary : Remove "Algebra`AnalyzeAndSolve`Private`" from output. *)
(* : Added for debugging for AnalyzeAndSolve by DB:01/14/2003 *)

CleanUpFunction = 
  ToExpression[
    StringReplace[ToString[InputForm[#]],
      { "Calculus`DDESpecialSolutions`Private`"->"",
        "Algebra`AnalyzeAndSolve`Private`"->""}
    ]
  ]&

(* This is the first call of AnalyzeAndSolve.  In this call, *)
(* The equations are converted into expressions equal to zero. *)
AnalyzeAndSolve[system: {HoldPattern[_ == _]..}, primaryunknowns_,
   secondaryunknowns_, parameters_, nonzeros_] :=
   AnalyzeAndSolve[(#[[1]]-#[[2]]&) /@ system, primaryunknowns,
      secondaryunknowns, parameters, nonzeros]

(* ************************************************************************ *)

(* Takes the newly recast version of AnalyzeAndSolve and converts its inputs *)
(* into a form readable by RecursivelyKeepTrack. *)
(* Warning: It is assumed that "system" is polynomial in "primaryunknowns", *)
(* "secondaryunknowns", and "parameters". *)

AnalyzeAndSolve[system_, primaryunknowns_, secondaryunknowns_, parameters_,
   nonzeros_] :=
   Block[{a, globalsol = {}, constraints},
      a = Together[({#}& /@ system) /. {{}}];
      constraints = (And @@ ((# != 0 &) /@ nonzeros));
      MapThread[
         RecursivelyKeepTrack[#1, #2, primaryunknowns, secondaryunknowns,
            parameters, nonzeros, constraints]&, {a, {{}}}];
      Union[globalsol]
   ]; (* end of block AnalyzeAndSolve *)

(* ************************************************************************ *)

(* Collects all the solutions at the end into globalsol. *)
(* Original code . . . replaced by the two following functions. *)

RecursivelyKeepTrack[{}, sol_, __] := (AppendTo[globalsol, sol]; {})

(* Terminates that recursive branch if the solution explodes *)
(* or becomes indeterminate. *)

RecursivelyKeepTrack[system_, sol_, __] /;
   (!FreeQ[system, DirectedInfinity] || !FreeQ[system, Indeterminate]) := {}

(* Main RecursivelyKeepTrack call.  It takes the system, cleans it up, *)
(* sorts it by complexity level (heuristic based on the degree of the *)
(* polynomial and size of the expression), takes first equation solves *)
(* it, simplifies the solution and recursively calls it self on each *)
(* unique branch of the solution. *)

RecursivelyKeepTrack[system_, sol_, primaryunknowns_, secondaryunknowns_,
   parameters_, nonzeros_, constraints_] :=
   Block[{a, b, c, recursiveDebug = False},
      (* Breaks the expression into a list and removes nonzeros and numbers. *)
      a = FactorListAndCleanUp[#, primaryunknowns, secondaryunknowns,
             parameters, nonzeros]& /@ system;
      (* Removes duplicates. Message added DB:05/23/2003 *)
      a = 
        Union[a] /. {} :> 
        (Message[AnalyzeAndSolve::soln, CleanUpFunction[sol]];{});
      (* Sorts the system by the "ComplexityLevel" heuristic which is the *)
      (* degree of the polynomial*100 + LeafCount size of the expression. *)
      a = Sort[a, (ComplexityLevel[#1, primaryunknowns, secondaryunknowns,
                      parameters] <=
                   ComplexityLevel[#2, primaryunknowns, secondaryunknowns,
                      parameters]&)];
      (* DB:01/14/2003 Print statement added for debugging. *)
      If[recursiveDebug,
        Print["The order of equations in the AnalyzeAndSolve routine is: "];
        Print[
          CleanUpFunction[
            {ComplexityLevel[#1, primaryunknowns, secondaryunknowns,
                        parameters],#1}& /@ a
          ]
        ];
      ];
      (* Takes the first equation of the system of equations (which is  *)
      (* the simplest according to the complexity heuristic) *)
      b = a[[1]];
      (* Then solves the first equation for only one variable. *)
      b = SolveStepByStep[#, primaryunknowns, secondaryunknowns, parameters,
                          constraints, sol]& /@ b;
      (* Flattens from the inside out:  {{{a,b},{c,d}}} -> {{a,b},{c,d}}. *)
      b = (Sequence @@ # &) /@ b;
      (* DB:02/04/2003 Added expand. *)
      b = MapAll[Factor, b];
      If[recursiveDebug,
        Print["The solution from the first equation is: "];
        Print[CleanUpFunction[ b ]];
      ];
      (* If there is no solution for the `simplest' equation, it terminates *)
      (* this recursive branch. *)
      If[Length[b] == 0, Return[{}]];
      (* Transposes the solution: {{a,b},{c,d}} -> {{a,c}, {b,d}} . *)
      b = Transpose[b];
      (* Adds constraints to the list, if there are any. .. && b && d *)
      c = (constraints && (And @@ #))& /@ b[[2]];
      (* Drops constraints. *)
      b = b[[1]];
      (* Applies the solution to the rest of the system and simplifies via *)
      (* a together and a numerator. *)
      a = Together[
             Internal`DeactivateMessages[Rest[a] /. b,
                Power::infy, General::indet
             ]
          ];
      a = Numerator[a];
      (* Removes any cases which it eliminates one of the other equations. *)
      a = DeleteCases[a, {___, 0, ___}, {2}];
      (* Takes the new solution, the one equation shorter system and the *)
      (* constraint and continues the recursive process. *)
      MapThread[
         RecursivelyKeepTrack[#1, #2, primaryunknowns, secondaryunknowns,
            parameters, nonzeros, #3]&, {a, b, c}]
   ]; (* end of block RecursivelyKeepTrack *)

(* ************************************************************************ *)

(* Performs a factor list and then removes from it any nonzeros or numbers. *)
(* Example: -4 + 8a - 4b + 8ab - b^2 + 2ab^2                                *)
(*          -> {{1, 1}, {-1 + 2*a, 1}, {2 + b, 2}}                          *)
(*          -> {{-1 + 2*a}, {2 + b}}                                        *)

FactorListAndCleanUp[
   system_, primaryunknowns_, secondaryunknowns_, parameters_, nonzeros_] :=
   Block[{a = FactorList /@ system},
      (* DB:02/04/2003 Remove terms that are non-zero. *)
      a = a /. ({#^_:1, _} :> Sequence[] & /@ nonzeros);
      (* DB:09/30/2003 Removes Tanh[3c[2]] type non-zero terms. *)
      a = a /. {Tanh[_ * c[_]]^_:1, _} :> Sequence[];
      (* DB:02/04/2003 Remove terms that are numeric. *)
      a = a /. {_?NumericQ, _} :> Sequence[];
      a = Flatten[Map[First[#]&, a, {2}]];
      Union[a]
   ]; (* end of block FactorListAndCleanUp *)

(* ************************************************************************ *)

(* New complexity analyzer by Douglas Baldwin on DB:02/03/2003 *)
ComplexityLevel[expr_List, primaryunknowns_, secondaryunknowns_, parameters_]:=
  Max[
    ComplexityLevel[#,primaryunknowns,secondaryunknowns,parameters] & /@ expr
  ] 

ComplexityLevel[expr_,primaryUnknowns_,secondaryUnknowns_,parameters_]:=
  Module[
    { primaryComplexity = Select[primaryUnknowns, !FreeQ[expr,#]&],
      secondaryComplexity= Select[secondaryUnknowns, !FreeQ[expr,#]&],
      parameterComplexity= Select[parameters, !FreeQ[expr,#]&],
      exprLength = If[Head[Expand[expr]] === Plus, Length[Expand[expr]], 1],
      complexityDebug = False
     },
    
    primaryComplexity  = Exponent[expr, primaryComplexity] ; 
    secondaryComplexity = Exponent[expr, secondaryComplexity];
    parameterComplexity = Exponent[expr, parameterComplexity]; 

    If[complexityDebug,
      Print["The precept sequence for the complexity analyzer is: "];
      Print[
        CleanUpFunction[{primaryComplexity, secondaryComplexity, 
           parameterComplexity, exprLength}
        ]
      ];
    ];
    Return[
      Min @@ 
       Flatten[{1*primaryComplexity, 2*secondaryComplexity, 
         3*parameterComplexity}] + exprLength
    ];
  ]; (* end of module ComplexityLevel *)

(* ************************************************************************ *)

(* This computes the leaves of the complexity analysis tree.              *)
(* The complexity heuristic (smaller is better) is either                *)
(*   (a) the exponent of the expression if it is polynomial, or           *)
(*   (b) 100*b*level + size of expression, where b is the number          *)
(*      of expressions which are of the level type (primary, secondary,  *)
(*      parameter), and the level: primary = 1, secondary = 2, param = 3 *)

SubComplexityLevel[expr_, a_, b_, level_] :=
   Block[{c = Select[a, PolynomialQ[expr, #]&]},
      Which[
         Length[c] == 0,
         100*b*level+LeafCount[expr],
         True,
         Min[Exponent[expr, c]]
      ]
   ]; (* end of block SubComplexityLevel *)

(* ************************************************************************ *)

(* Solves a single equation *)
(* Takes the factor terms which have the primary unknowns and pass it *)
(* on to the SubSolveStepByStep to be solved along with the secondary *)
(* unknowns, parameters, constraints and solutions. *)

SolveStepByStep[eqn_, primaryunknowns_, secondaryunknowns_, parameters_,
   constraints_, sol_] :=
   Block[{a},
      a = Union[Cases[{eqn}, q_ /; MemberQ[primaryunknowns, q], -1]];
      (
       SubSolveStepByStep[eqn, a, 
          Flatten[{secondaryunknowns, parameters}],
          constraints, sol
       ]
      ) /; Length[a] != 0
   ]; (* end of block SolveStepByStep *)

(* ************************************************************************ *)

(* Takes the factor terms which have the secondaryunknowns and pass it *)
(* on to the SubSolveStepByStep to be solved along with parameters,  *)
(* constraints and solutions. *)

SolveStepByStep[eqn_, primaryunknowns_, secondaryunknowns_, parameters_,
   constraints_, sol_] :=
   Block[{a},
      a = Union[Cases[{eqn}, q_ /; MemberQ[secondaryunknowns, q], -1]];
      (
       SubSolveStepByStep[eqn, a, parameters, constraints, sol]
      ) /; Length[a] != 0
   ]; (* end of block SolveStepByStep *)

(* ************************************************************************ *)

(* Takes the factor terms which have the parameters and pass it on to the *)
(* SubSolveStepByStep to be solved along with constraints and solutions. *)

SolveStepByStep[eqn_, primaryunknowns_, secondaryunknowns_, parameters_,
   constraints_, sol_] :=
   Block[{a},
      a = Union[Cases[{eqn}, q_ /; MemberQ[parameters, q], -1]];
      (
       SubSolveStepByStep[eqn, a, {}, constraints, sol]
      ) /; Length[a] != 0
   ]; (* end of block SolveStepByStep *)

(* ************************************************************************ *)

(* Takes anything that isn't composed of primary unknowns, secondary *)
(* unknowns, or parameters and returns an empty set. *)

SolveStepByStep[___] := {};

(* Takes the equation and primary unknowns (which are either THE primary *)
(* unknowns, THE secondary unknowns, or THE parameters from above).  *)
(* 1. If the equation is polynomial in any of the unknowns, it selects *)
(*    them and sorts them by power/exponent and then includes the unknowns *)
(*    that the equation is not polynomial in.  If the equation is not *)
(*    polynomial in any of the unknowns, it takes the order that they *)
(*    were given in.  *)
(* 2. Uses Reduce to solve the equation (along with find the constraints). *)
(* 3. Then it converts the results to rules (same form as Solve) and *)
(*    returns an empty list if it is empty. *)
(* 4. If there is a solution, it removes a != b type results from the *)
(*    form of the solution outputted by Reduce. *)
(* 5. It then applies the results of the solution to the rest of the *)
(*    solution. *)
(* 6. Formats the solution so that each sublist contains the latest solution *)
(*    branches along with the previous solutions in a flattened and unique *)
(*    list. *)

SubSolveStepByStep[eqn_, primaryunknowns_, pars_, constraints_, sol_] :=
   Block[{a, b, c},
      a = Select[primaryunknowns, PolynomialQ[eqn, #]&];
      If[Length[a] != 0,
         a = Sort[a, Exponent[eqn, #1] <= Exponent[eqn, #2]&];
         a = Flatten[{a, Complement[primaryunknowns, a]}],
         a = primaryunknowns
      ];
      c = myReduce[eqn == 0 && constraints, Flatten[{a, pars}]];
      a = {ToRules[c]};
      If[Length[a] == 0, Return[{}]];
      c = Cases[{#}, p_ != q_, -1]& /@ If[Head[c] === Or, List @@ c, {c}];
      b = Internal`DeactivateMessages[sol /. a, Power::infy, General::indet];
      Union[Transpose[{Flatten /@ Thread[{b, a}, List, 2], c}]]
   ]; (* end of block SubSolveStepByStep *)

(* ************************************************************************ *)

End[] (* `Private` context *)

SetAttributes[AnalyzeAndSolve, ReadProtected]

EndPackage[]

END OLD ANALYZESOLVE OF 2003 *)

(* START NEW ANALYZESOLVE OF 2010 *)

(* ************************************************************************ *)
(* : Title : AnalyzeAndSolveV2.m 
*  : Author : Douglas Baldwin, Unal Goktas, and Willy Hereman
*  : Email : solve@douglasbaldwin.com
*  : Date Modified : Thursday, March 4, 2010 by Douglas Baldwin
*  : History : First developed by Unal Goktas (WRI) and Willy Hereman and 
*    written by Unal Goktas in October/November 2000; 
*    comments added and complexity analyzer redesigned by Douglas Baldwin 
*    in February 2003; 
*    redesigned by DB in February 2007 to use depth-first search rather than 
*    a recursive breadth-first search; 
*    DB finished redesign in March 2010. *)

(* ************************************************************************ *)

BeginPackage["Algebra`AnalyzeAndSolve`"]

Unprotect[AnalyzeAndSolve]

AnalyzeAndSolve::soln = "The solution `1` is being removed because it is 
inconsistent."

Begin["`Private`"]

If[$VersionNumber < 4,
   Attributes[Internal`DeactivateMessages] = {HoldAll};
   Internal`DeactivateMessages[body_, msgs___MessageName] :=
      Module[{wasOn = Select[Hold[msgs], Head[#] =!= $Off &], result},
         CheckAbort[
            Scan[Off, wasOn];
            result = body;
            Scan[On, wasOn];
            result,
            Scan[On, wasOn];
            Abort[]
         ]
      ] (* end of module Internal`DeactivateMessages *)
]; (* end of if versionnumber < 4 *)

If[$VersionNumber >= 5,
	(* DB:1/8/2010 Added Version 7.0+ check. *)
	If[$VersionNumer >= 7,
		 SetSystemOptions[
			"ReduceOptions" -> {"ReorderVariables" -> False}
		 ],
		 Developer`SetSystemOptions[
			"ReduceOptions" -> {"ReorderVariables" -> False}
		 ]]; (* end if versionnumber >= 7 *)
   myReduce[eqn_, vars_] :=
    LogicalExpand[
      Reduce[eqn, Reverse[vars]] /. Equal -> myEqual
    ] /. myEqual -> Equal,
   myReduce[eqn_, vars_] := Reduce[eqn, vars, Sort -> False]
]; (* end if versionnumber >= 5 *)

(* ************************************************************************ *)

(* : Title : CleanUpFunction *)
(* : Author : Douglas Baldwin *)
(* : Summary : Remove "Algebra`AnalyzeAndSolve`Private`" from output. *)
(*    Added for debugging for AnalyzeAndSolve by DB:1/14/2003 *)

CleanUpFunction = 
  ToExpression[
    StringReplace[ToString[InputForm[#]],
      { "Calculus`PDESpecialSolutions`Private`"->"",
        "Calculus`DDESpecialSolutions`Private`"->"",
        "Algebra`AnalyzeAndSolve`Private`"->""}
    ]
  ]&

(* ************************************************************************ *)

(* : Title : AnalyzeAndSolve *)
(* : Author : Douglas Baldwin *)
(* : Summary : Takes a list of equations which depend on primary unknowns, 
*  secondary unknowns, and parameters and solves for the unknowns and 
*  parameters in an depth-first search which takes advantage of the given 
*  nonzero unknowns to simplify the expressions. *)

AnalyzeAndSolve[system_, primaryunknowns_, secondaryunknowns_, 
      parameters_, nonzeros_] :=
   Block[{  sys = system /. Equal[a_,b_]:>a-b, (* A local copy of system. *)
            constraints, (* Constraints on the possible solutions. *)
            theList, (* The search tree. *)
            soln = {}, (* The solution. *)
            currentSystem, (* The system of equations to be solved. *)
            currentSolutions, (* Expressions for known variables. *)
            currentSoln, (* The new solution from the simplest equation. *)
            currentConstraints, (* The constraints on future solutions. *)
            theNextNode, (* The next node to be expanded. *)
            depthFirstSolveDebug = False,
            recursiveDebug = False
         }, (* Protected local variables. *)
			sys = Numerator[Together[({#}& /@ sys)]];
      (* Takes the nonzeros given by the user and puts them in the form *)
      (* needed by Reduce. *)
      constraints = (And @@ ((# != 0 &) /@ nonzeros));

      (* The first node of the search tree. *)
      theList = {{{sys,{},constraints}}};

      While[True, (* Begin While A1 *)

         If[( !FreeQ[theList[[-1,1,1]], DirectedInfinity] || 
               !FreeQ[theList[[-1,1,1]], Indeterminate] || 
               !FreeQ[theList[[-1,1,1]], False] ),

               (* Goes back to the next branch. *)
               While[ Length[theList[[-1]]] === 1, 
                  theList = Drop[theList,-1]; 
                  (* If all branches have been searched, return soln. *)
                  If[ Length[theList] === 0, Return[soln] ];
               ];
               
               (* Removes the branch just solved for. *)
               theList = 
                  Append[Drop[theList,-1], Rest[theList[[-1]]]];

               If[depthFirstSolveDebug,
                 Print["The pruned search tree:"];
                 Print[CleanUpFunction[ theList ]];
               ];
         ];           

        
         If[theList[[-1,1,1]] === {}, (* Begin If A2 *)
(* * * * * * * * * * * * * *  If TRUE of If A2 * * * * * * * * * * * * * *  *)
               If[depthFirstSolveDebug,
                 Print["The current search tree is:"];
                 Print[CleanUpFunction[ theList ]];
               ];

               (* Adds new solution to soln. *)
               AppendTo[soln, theList[[-1,1,2]] ];

               If[depthFirstSolveDebug,
                 Print["The complete set of solutions is:"];
                 Print[CleanUpFunction[ soln ]];
               ];

               (* Goes back to the next branch. *)
               While[ Length[Last[theList]] === 1, 
                  theList = Drop[theList,-1]; 
                  (* If all branches have been searched, return soln. *)
                  If[ Length[theList] === 0, Return[soln] ];
               ];
               
               (* Removes the branch just solved for. *)
               theList =   
                  Append[Drop[theList,-1], Rest[theList[[-1]]]];

               If[depthFirstSolveDebug,
                 Print["The pruned search tree:"];
                 Print[CleanUpFunction[ theList ]];
               ],
(* * * * * * * * * * * * * *  If FALSE of If A2 * * * * * * * * * * * * * *  *)

               (* Applies the current solutions to the system. *)
               currentSystem = 
		 FactorListAndCleanUp[#, primaryunknowns, secondaryunknowns,
		       parameters, nonzeros]& /@ theList[[-1,1,1]];
               (* Pulls off the first solution of each list. *)
               currentSolutions = theList[[-1,1,2]];
               (* Pulls off the corresponding contraints on *)
               (* the above solutions. *)
               currentConstraints = theList[[-1,1,3]];

               If[depthFirstSolveDebug,
                 Print["The last entry in theList is:"];
                 Print[CleanUpFunction[ Last[theList] ]];
                 Print["The current system is:"];
                 Print[CleanUpFunction[ currentSystem ]];
                 Print["The current list of solutions is:"];
                 Print[CleanUpFunction[ currentSolutions ]];
                 Print["The current list of contraints is:"];
                 Print[CleanUpFunction[ currentConstraints ]];
               ];

               (* Removes duplicates. Message added DB:5/23/2003 *)
               currentSystem = 
                 Union[currentSystem] /. {} :> 
                 (Message[AnalyzeAndSolve::soln, 
                          CleanUpFunction[currentSolutions]];{});

               If[depthFirstSolveDebug,
                 Print["The system after duplicates are removed is:"];
                 Print[CleanUpFunction[ currentSystem ]];
               ];

               (* Sorts the system by the "ComplexityLevel" heuristic. *)
               (* DB:3/2/2010 Changed back to Sort[List, Test]. *)
               currentSystem = 
                 Sort[currentSystem, 
                   (ComplexityLevel[#1, primaryunknowns, 
                        secondaryunknowns, parameters] <=
                      ComplexityLevel[#2, primaryunknowns, 
                          secondaryunknowns, parameters]&)];
               (* DB:1/14/2003 Print statement added for debugging. *)
               If[depthFirstSolveDebug || recursiveDebug,
                 Print["The order of the equations in AnalyzeAndSolve is: "];
                 Print[
                   CleanUpFunction[
                     {ComplexityLevel[#1, primaryunknowns, secondaryunknowns,
                                 parameters],#1}& /@ currentSystem
                   ]
                 ];
               ];

               (* Takes the first equation of the system of equations (which *)
               (* is the simplest according to the complexity heuristic) *)
               (* and then solves it for only one variable. *)
               currentSoln = 
                  SolveStepByStep[#, primaryunknowns, 
                     secondaryunknowns, parameters, currentConstraints, 
                     currentSolutions]& /@ currentSystem[[1]];
		     (* Flattens from the inside out:  
                        {{{a,b},{c,d}}} -> {{a,b},{c,d}}. *)
			currentSoln = (Sequence @@ # &) /@ currentSoln;
			currentSoln = 
                               currentSoln /. (p_ -> q_) :> (p -> Factor[q]);
			       If[depthFirstSolveDebug || recursiveDebug,
                 Print["The solution from the first equation is:"];
                 Print[CleanUpFunction[ currentSoln ]];
               ];

               (* If there is no solution for the `simplest' equation, *)
               (* it terminates this branch of the search tree. *)
               If[Length[currentSoln] == 0, (* Begin If A3 *)
(* * * * * * * * * * * * * *  If TRUE of If A3 * * * * * * * * * * * * * *  *)
                  (* Goes back to the next branch. *)
                  While[ Length[Last[theList]] === 1, 
                     theList = Drop[theList,-1]; 
                     (* If all branches have been searched, return soln. *)
                     If[ Length[theList] === 0, Return[soln] ];
                  ];
                  
                  theList =   
                    Append[Drop[theList,-1], Rest[theList[[-1]]]];

                  If[depthFirstSolveDebug,
                    Print["The pruned search tree:"];
                    Print[CleanUpFunction[ theList ]];
                  ],  
(* * * * * * * * * * * * * * If FALSE of If A3 * * * * * * * * * * * * * *  *)
                  (* Transposes the solution: 
                     {{a,b},{c,d}} -> {{a,c}, {b,d}} *)
                  currentSoln = Transpose[currentSoln];
                  (* Adds constraints to the list, if there are any. .. 
                                                   && b && d *)
                  currentConstraints = 
                     (currentConstraints && (And @@ #))& /@ currentSoln[[2]];
                  (* Drops constraints. *)
                  currentSoln = currentSoln[[1]];
                  (* Applies the solution to the rest of the system *)
                  (* and simplifies via a together and a numerator. *)
                  currentSystem = Together[
                         Internal`DeactivateMessages[
                            Rest[currentSystem] /. currentSoln,
                            Power::infy, General::indet
                         ]
                      ];
                  currentSystem = Numerator[currentSystem];

                  If[depthFirstSolveDebug,
                    Print["The current system is:"];
                    Print[CleanUpFunction[ currentSystem ]];
                  ];

                  (* Breaks the expression into a list and removes 
                                nonzeros and numbers. *)
                  currentSystem = Numerator[currentSystem];
                  (* If any of the equations are satisfied, remove them. *)
                  currentSystem = 
                         DeleteCases[currentSystem, {___, 0, ___}, {2}];

                  (* Reformat for the system and solutions to be passed 
                                                 as the next node. *)
                  theNextNode = 
                     MapThread[ {#1, #2, #3}&,
                           {currentSystem, currentSoln, currentConstraints}];
                  (* Remove any invalid solutions. *)
                  theNextNode = 
			DeleteCases[theNextNode, 
                        {a_List,_List,_And} /; 
                           (!FreeQ[a, DirectedInfinity] || 
                            !FreeQ[a, Indeterminate]),
                        {2}];

                  If[depthFirstSolveDebug,
                     Print["The current (cleaned up) system is:"];
                     Print[CleanUpFunction[ currentSystem ]];
                     Print["The theList argument being passed to the next 
                            depthFirstSolve is:"];
                     Print[CleanUpFunction[ Append[theList,theNextNode ] ]];
                  ];

                  (* Takes the new solution, the one equation shorter system 
                                             and the *)
                  (* constraint and continues to the next step lower node. *)
                  AppendTo[theList, theNextNode];
               ]; (* End If A3 *)
         ]; (* End If A2 *)
      ]; (* End While A1 *)

   ] (* end of block AnalyzeAndSolve *)

(* ************************************************************************ *)

(* Performs a factor list and then removes from it any nonzeros or numbers. *)
(* Ex: -4 + 8a - 4b + 8ab - b^2 + 2ab^2 *)
(*    -> {{1, 1}, {-1 + 2*a, 1}, {2 + b, 2}} *)
(*     -> {{-1 + 2*a}, {2 + b}} *)
FactorListAndCleanUp[
   system_, primaryunknowns_, secondaryunknowns_, parameters_, nonzeros_] :=
   Block[{a = FactorList /@ system},
      (* DB:2/4/2003 Remove terms that are non-zero. *)
      a = a /. ({#^_:1, _} :> Sequence[] & /@ nonzeros);
      (* DB:2/4/2003 Remove terms that are numeric. *)
      a = a /. {_?NumericQ, _} :> Sequence[];
      a = Flatten[Map[First[#]&, a, {2}]];
      Union[a]
   ]; (* end of block FactorListAndCleanUp *)

(* ************************************************************************ *)

(* New complexity analyzer by Douglas Baldwin on DB:2/3/2003 *)
ComplexityLevel[expr_List, primaryunknowns_, secondaryunknowns_, parameters_]:=
  Max[
    ComplexityLevel[#,primaryunknowns,secondaryunknowns,parameters] & /@ expr
  ] 

ComplexityLevel[expr_,primaryUnknowns_,secondaryUnknowns_,parameters_]:=
  Module[
    { primaryComplexity = Select[primaryUnknowns, !FreeQ[expr,#]&],
      secondaryComplexity= Select[secondaryUnknowns, !FreeQ[expr,#]&],
      parameterComplexity= Select[parameters, !FreeQ[expr,#]&],
      exprLength = If[Head[Expand[expr]] === Plus, Length[Expand[expr]], 1],
      complexityDebug = False
     },
    
    primaryComplexity  = Exponent[expr, primaryComplexity] ; 
    secondaryComplexity = Exponent[expr, secondaryComplexity];
    parameterComplexity = Exponent[expr, parameterComplexity]; 

    If[complexityDebug,
      Print["The precept sequence for the complexity analyzer is: "];
      Print[
        CleanUpFunction[{primaryComplexity, secondaryComplexity, 
           parameterComplexity, exprLength}
        ]
      ];
    ];
    Return[
      Min @@ 
       Flatten[{1*primaryComplexity, 2*secondaryComplexity, 
         3*parameterComplexity}] + exprLength
    ];

  ]; (* end of module ComplexityLevel *)

(* ************************************************************************ *)

(* This computes the leaves of the complexity analysis tree. *)
(* The complexity heuristic (smaller is better) is either *)
(*   (a) the exponent of the expression if it is polynomial, or *)
(*   (b) 100*b*level + size of expression, where b is the number *)
(*      of expressions which are of the level type (primary, secondary, *)
(*      parameter), and the level: primary = 1, secondary = 2, param = 3 *)
SubComplexityLevel[expr_, a_, b_, level_] :=
   Block[{c = Select[a, PolynomialQ[expr, #]&]},
      Which[
         Length[c] == 0,
         100*b*level+LeafCount[expr],
         True,
         Min[Exponent[expr, c]]
      ]
   ]; (* end of block SubComplexityLevel *)

(* ************************************************************************ *)

(* solves a single equation *)

(* Takes the factor terms which have the primary unknowns and pass it *)
(* on to the SubSolveStepByStep to be solved along with the secondary *)
(* unknowns, parameters, constraints and solutions. *)
SolveStepByStep[eqn_, primaryunknowns_, secondaryunknowns_, parameters_,
   constraints_, sol_] :=
   Block[{a},
      a = Union[Cases[{eqn}, q_ /; MemberQ[primaryunknowns, q], -1]];
      (
       SubSolveStepByStep[eqn, a, 
          Flatten[{secondaryunknowns, parameters}],
          constraints, sol
       ]
      ) /; Length[a] != 0
   ]; (* end of block SolveStepByStep 1 *)

(* ************************************************************************ *)

(* Takes the factor terms which have the secondaryunknowns and pass it *)
(* on to the SubSolveStepByStep to be solved along with parameters,  *)
(* constraints and solutions. *)
SolveStepByStep[eqn_, primaryunknowns_, secondaryunknowns_, parameters_,
   constraints_, sol_] :=
   Block[{a},
      a = Union[Cases[{eqn}, q_ /; MemberQ[secondaryunknowns, q], -1]];
      (
       SubSolveStepByStep[eqn, a, parameters, constraints, sol]
      ) /; Length[a] != 0
   ]; (* end of block SolveStepByStep 2 *)

(* ************************************************************************ *)

(* Takes the factor terms which have the parameters and pass it on to the *)
(* SubSolveStepByStep to be solved along with constraints and solutions. *)
SolveStepByStep[eqn_, primaryunknowns_, secondaryunknowns_, parameters_,
   constraints_, sol_] :=
   Block[{a},
      a = Union[Cases[{eqn}, q_ /; MemberQ[parameters, q], -1]];
      (
       SubSolveStepByStep[eqn, a, {}, constraints, sol]
      ) /; Length[a] != 0
   ]; (* end of block SolveStepByStep 3 *)

(* ************************************************************************ *)

(* Takes anything that isn't composed of primary unknowns, secondary *)
(* unknowns, or parameters and returns an empty set. *)
SolveStepByStep[___] := {}

(* Takes the equation and primary unknowns (which are either THE primary *)
(* unknowns, THE secondary unknowns, or THE parameters from above).  *)
(* 1. If the equation is polynomial in any of the unknowns, it selects *)
(*    them and sorts them by power/exponent and then includes the unknowns *)
(*    that the equation is not polynomial in.  If the equation is not *)
(*    polynomial in any of the unknowns, it takes the order that they *)
(*    were given in.  *)
(* 2. Uses Reduce to solve the equation (along with find the constraints). *)
(* 3. Then it converts the results to rules (same form as Solve) and *)
(*    returns an empty list if it is empty. *)
(* 4. If there is a solution, it removes a != b type results from the *)
(*    form of the solution outputted by Reduce. *)
(* 5. It then applies the results of the solution to the rest of the *)
(*    solution. *)
(* 6. Formats the solution so that each sublist contains the latest solution *)
(*    branches along with the previous solutions in a flattened and unique *)
(*    list. *)

SubSolveStepByStep[eqn_, primaryunknowns_, pars_, constraints_, sol_] :=
   Block[{a, b, c},
      a = Select[primaryunknowns, PolynomialQ[eqn, #]&];
      If[Length[a] != 0,
         a = Sort[a, Exponent[eqn, #1] <= Exponent[eqn, #2]&];
         a = Flatten[{a, Complement[primaryunknowns, a]}],
         a = primaryunknowns
      ];
      c = myReduce[eqn == 0 && constraints, Flatten[{a, pars}]];
      a = {ToRules[c]};
      If[Length[a] == 0, Return[{}]];
      c = Cases[{#}, p_ != q_, -1]& /@ If[Head[c] === Or, List @@ c, {c}];
      b = Internal`DeactivateMessages[sol /. a, Power::infy, General::indet];
      Union[Transpose[{Flatten /@ Thread[{b, a}, List, 2], c}]]
   ]; (* end of block SubSolveStepByStep *)

(* ************************************************************************ *)

End[] (* `Private` context *)

SetAttributes[AnalyzeAndSolve, ReadProtected]

EndPackage[]

Print["Package AnalyzeAndSolveV2.m of March 13, 2010 was successfully loaded."];

(* ************************************************************************ *)

(* END NEW ANALYZESOLVE OF 2010 *)

Print["Package DDESpecialSolutionsV2.m was successfully loaded."];
Print["Version 2 was last updated: March 20, 2010 by Hereman."];
(* Print[" "]; *)
Print["Previously updated: Friday, January 23, 2009 by Hereman."];
Print["Version 1 was first released on July 23, 2004."];

(* ------------------------------------------------------------------------- *)

(* ***************************** end of all ******************************** *)

