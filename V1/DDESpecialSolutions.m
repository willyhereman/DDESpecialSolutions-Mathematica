(* FINAL VERSION *)
(* ************************************************************************ *)

(* : Title : DDESpecialSolutions.m
*  : Authors : Douglas Baldwin, Unal Goktas, and Willy Hereman.
*    Department of Mathematical and Computer Sciences
*    Colorado School of Mines
*    Golden, Colorado 80401-1887, U.S.A
*    Contact email: whereman@mines.edu

*  : Last updated : 12-21-2001 at 21:30 by Hereman.
*  : Summary : Solves systems of nonlinear differential-difference equations
     (DDEs) also called lattices, in terms of the hyperbolic function Tanh.
*  : Warnings : This package uses the assumption that Sqrt[a^2] -> a, etc.
*    (see MySimplificationRules below) when simplifying. *)

(* ************************************************************************ *)

(* Algorithm and implementation by Douglas Baldwin, *)
(* Unal Goktas (WRI) and Willy Hereman. *)
(* Copyright 2001 *)

BeginPackage["Calculus`DDESpecialSolutions`"]

Unprotect[DDESpecialSolutions]

DDESpecialSolutions::usage = 
"DDESpecialSolutions[eqns, funcs, vars, params, opts] solves a system of 
nonlinear differential-difference equations for funcs, with 
independent variables vars ({n,t}) and non-zero parameters params.
\[NewLine]DDESpecialSolutions takes the options NumericTest and SymbolicTest
with the default values False.
\[NewLine]If NumericTest is set to True, DDESpecialSolutions test the possible
solutions based on 13 different sets of random numbers ranging from
zero to one for all parameters and remaining constants.  Solutions are
accepted if they pass one or more of the these tests.
\[NewLine]If SymbolicTest is set to True, the solutions are tested
truly symbolically and the results of the test are shown in factored form.
\[NewLine]DDESpecialSolutions also takes the option InputForm with the 
default value True. If InputForm is set to False, the output of 
DDESpecialSolutions will be in standard Mathematica output form."

DDESpecialSolutions::poly = "This system must be a polynomial of fixed order."

DDESpecialSolutionsmSolver::freedom = "Freedom exists in this system, as `1` 
are both dominant powers in expression `2`."

DDESpecialSolutionsmSolver::fail = "The algorithm failed while attempting 
to find the positive integer values of m[n]."

DDESpecialSolutionsmSolver::noSoln = "mSolver did not find any positive 
integer values for the dominate behavior, and will now test the values from 
1 to 3 to see if the package missed a solution due to inequalities."

DDESpecialSolutions::solve = "The algorithm failed while attempting to find 
the coefficients for the polynomial solution."

(* Options definition. *)

Options[DDESpecialSolutions] = 
  {Verbose -> False, InputForm -> True, NumericTest -> False,
   SymbolicTest -> False, DegreeOfThePolynomial -> {}}

Begin["`Private`"]

(* If called with non-lists, makes them lists. *)

DDESpecialSolutions[eqns_?(!ListQ[#]&), funcs_, vars_, param_, 
  opts___?OptionQ]:=
  DDESpecialSolutions[{eqns}, funcs, vars, param, opts]

DDESpecialSolutions[eqns_, funcs_?(!ListQ[#]&), vars_, param_, 
  opts___?OptionQ]:=
  DDESpecialSolutions[eqns, {funcs}, vars, param, opts]

DDESpecialSolutions[eqns_, funcs_, vars_?(!ListQ[#]&), param_, 
  opts___?OptionQ]:=
  DDESpecialSolutions[eqns, funcs, {vars}, param, opts]

DDESpecialSolutions[eqns_, funcs_, vars_, param_?(!ListQ[#]&),
  opts___?OptionQ]:=
  DDESpecialSolutions[eqns, funcs, vars, {param}, opts]

(* ************************************************************************ *)

(* Start of function. *)

DDESpecialSolutions[eqns_List, funcs_List, vars_List, param_List, 
  opts___?OptionQ]:=
  Block[
    {testarg = FreeQ[MapAll[Expand, eqns], (Power[b__, a__] /; 
       (!FreeQ[a, _Symbol] | MemberQ[b, _Real | _Integer])) ],
     numberOfEquations,
     VerboseTest = Verbose /. {opts} /. Options[DDESpecialSolutions],
     time = TimeUsed[],
     system,
     mSoln,
     newSystem,
     solution}, (* Protected Local Variables *)

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
              Flatten[
                {{x}[[1]],
                 ",",
                Table[#[[1]], {#[[2]]}
                ]& /@ Transpose[{{x}, {n}}]
                }
              ]
            ]
          ],
          Sequence @@ (
            (Head[#][x__] :> 
              Subscript[Head[#],{x}[[1]] ]
            )& /@ funcs)
        }
      ]
    ];

    (* Step D1 in the paper. *)
    (* Transforms the DDE into a nonlinear DDE in $T$ *)
    If[VerboseTest,
      Print["Transform the DDE into a nonlinear DDE in T=Tanh."]
    ];

    system = 
      DDESpecialSolutionsVarChange[eqns /. (a__==b__):>(a-b),funcs, vars];

    If[VerboseTest,
      Print[DDESpecialSolutionsCleanUp[system /. myTrackingVariable[_]->1]];
      Print["Time Used:", TimeUsed[]-time]
    ];

    time = TimeUsed[];

    (* Step D2 in the paper. *)
    (* Determines the maximal degree of the polynomial solutions. *)
    If[VerboseTest,
      Print["Determine the maximal degree of the polynomial solutions."]
    ];

    mSoln =
      Internal`DeactivateMessages[
        DDESpecialSolutionsmSolver[system, vars, opts], 
        Solve::svars
      ];
    If[Length[mSoln] === 0,
      Message[DDESpecialSolutionsmSolver::fail];Return[{}]
    ];

    If[VerboseTest,
      Print[DDESpecialSolutionsCleanUp[
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
    If[VerboseTest,
      Print["Derive the nonlinear algebraic system for the coefficients."]
    ];

    newSystem = 
      DDESpecialSolutionsBuildSystem[mSoln, system, vars, param, opts];

    If[VerboseTest,
      Print["The nonlinear algebraic system is:"];
      Print[DDESpecialSolutionsCleanUp[newSystem /. myTrackingVariable[_]->1]];
      Print["Time Used:", TimeUsed[]-time]
    ];

    time = TimeUsed[];

    (* Step D4 in the paper. *)
    (* Solve the nonlinear parameterized system. *)
    If[VerboseTest,
      Print["Solve the nonlinear algebraic system."]
    ];

    solution = 
        Algebra`AnalyzeAndSolve`AnalyzeAndSolve @@ #& /@ newSystem;
    If[Length[Flatten[solution]] === 0,
      Message[DDESpecialSolutions::solve];Return[{}];
    ];

    If[VerboseTest,
      Print[DDESpecialSolutionsCleanUp[solution]];
      Print["Time Used:", TimeUsed[]-time]
      ];

    time = TimeUsed[];

    (* Step D5 in the paper. *)
    (* Build and test the solitary wave solutions. *)
    If[VerboseTest,
      If[( (SymbolicTest /. {opts} /. Options[DDESpecialSolutions]) ||
           (NumericTest /. {opts} /. Options[DDESpecialSolutions]) ),
        Print["Build and also test the travelling wave solutions."], (* else *)
        Print["Build the travelling wave solutions."]
      ]
    ];

    solution = 
    DDESpecialSolutionsBuildSolutions[solution, mSoln, eqns, funcs, 
       vars, param, opts];

    If[VerboseTest,
      Print[DDESpecialSolutionsCleanUp[solution]];
      Print["Time Used:", TimeUsed[]-time];
      Print[];
     If[( (SymbolicTest /. {opts} /. Options[DDESpecialSolutions]) ||
           (NumericTest /. {opts} /. Options[DDESpecialSolutions]) ),
       Print["The (numerically and/or symbolically) tested final solutions:"],
       Print["The list of possible solutions:"]
      ];
    ];

    (* Returns solutions to user. *)
    Return[
      If[InputForm /. {opts} /. Options[DDESpecialSolutions],
        InputForm[DDESpecialSolutionsCleanUp[solution]],
        DDESpecialSolutionsCleanUp[solution]
      ]
    ];

  ) /; testarg
  ];

(* ************************************************************************ *)

(* : Title : DDESpecialSolutionsVarChange *)
(* : Author : Douglas Baldwin *)
(* : Input : The equation list (F[i][n,t]) and the form tanh. *)
(* : Output : The system in the form u[i][T] depending on whether 
     it is tanh. *)
(* : Summary : Converts from real space-time domain to u[i][T]. *)

DDESpecialSolutionsVarChange[eqns_List, funcs_List, vars_List]:=
  Block[{funcRules, (* conversion from user functions *)
        i=0, (* Iterator for myTrackingVariables *)
        eqList, (* The list of equations, in a usable form *)
        system (* The system after transform to DDE in T *)
        }, (* Protected Local Variables *)

    (* Creates a set of rules to converts the users functions *)
    (* (e.g., u[n,t]) to varChangeFunction[i][n,t]. *)
    funcRules = 
      Table[
        Head[funcs[[i]] ] -> varChangeFunction[i],
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
      varChangeFunction[n_][var_,_] :> u[n][var][T],
      Derivative[_,a_][varChangeFunction[n_]][var_,_] :>  
        Expand[
              Nest[c[2]*(1-T^2)*D[#, T]&,
                u[n][var][T], 
                a
              ]
            ]
      };

    (* Simplifies the system by removing extra (1-T^2)'s *)
    (* and T's from the system. *)
    system = 
      If[(# /. T->-1) === 0 && (# /. T->1) === 0, 
        Factor[#/(1-T^2)], Factor[#]]& /@ system;
    system = 
      If[(# /. T->0) === 0, 
        Factor[#/T], Factor[#]]& /@ system;
 
    (* Returns the system back to the DDESpecialSolutions *)
    Return[MapAll[Factor, system]];
  ];

(* ************************************************************************ *)

(* : Title : DDESpecialSolutionsmSolver *)
(* : Author : Douglas Baldwin *)
(* : Input : The system generated by varChange. *)
(* : Output : The power series solutions for u[i][T], id est 
     u[i][T] = a[1,0]+a[1,1]*T+a[1, 2]*T^2+...+a[1,m]*T^m. *)

DDESpecialSolutionsmSolver[system_List, vars_List, opts___?OptionQ] := 
  Block[{numberOfEquations, 
         myTrackingVariableMax,
         replaceRules, 
         eqnList, 
         mList0,
         mList, 
         mListStructure, 
         perm, 
         comboList, 
         mRules, 
         time = TimeUsed[],
         comboList2, 
         VerboseTest = Verbose /. {opts} /. Options[DDESpecialSolutions],
         mSoln2, 
         freeVariable, 
         freeVariableMax,
         mSolnFree, 
         mSoln, 
         mSoln0, 
         checkList2}, (* Protects Local Variables *)

    (* Sets numberOfEquations to the length number of equations. *)
    numberOfEquations = Length[system];

    (* Determines the number of myTrackingVariables *)
    myTrackingVariableMax = 0;
    system /. myTrackingVariable[a_Integer] :> 
      myTrackingVariable[
        If[a > myTrackingVariableMax, myTrackingVariableMax++]; a];

    (* Creates rules which will be used to replace the *)
    (* functions passed to mSolve to those of $T^{m_i}$ *)
    replaceRules = 
      u[n_][vars[[1]]+p_Integer:0] :> 
        Function[{F}, ((F+Tanh[p*c[1]])/(1+F*Tanh[p*c[1]]))^m[n]];

    (* Uses the replaceRules to convert to functions of T *)
    eqnList0 = 
      Expand[
        DeleteCases[Flatten[system /. replaceRules], 
          0, 
          Infinity
        ]
      ];

    (* Breaks up expressions into lists of terms. *)
    eqnList = If[Head[#]===Plus, List @@ #, {#}]& /@ eqnList0;

    (* Pulls off the exponents of T and forms a list *)
    (* of expressions of the form {{{1+m[1]},{..}..}..}  *)
    mList0 = Exponent[#, T]& /@ #& /@ eqnList;

    (* The following lines breaks up the list of exponents *)
    (* of T and then removes invalid cases. *)

    (* Breaks up the expressions of $a+b\,m_i+c\,m_j+\dotsc$ *)
    (* where $a,b,c,\dotsc,i,j,k,\dotsc\in\mathbb{R}$ into lists. *)
    mList = 
      Map[
        If[Head[#]===Plus, 
          List @@ #, 
          If[Head[#]===m || Head[#]===Times, 
            {#}, 
            #
          ]
        ]&, 
        mList0, 
        2
      ];

    (* The following routine strips off the $a$ in the above *)
    (* expression and leaves only the underlying structure. *)
    mListStructure = 
      Union[# /. {a_Integer, b__}:>{b}& /@ #]& /@ mList;

    (* Re-organizes the list of powers of T by the structure *)
    (* listed above. *)
    mList = 
      Table[
        Flatten[
          Table[
            Cases[#, 
              Flatten[{_, mListStructure[[i,j]]}] |
              mListStructure[[i,j]] 
            ]& /@ {mList[[i]]}, 
            {j, Length[mListStructure[[i]] ]}
          ], 
          1
        ], 
        {i, numberOfEquations}
      ];

    (* Determines the maximum $a$ in each power of T *)
    mList = 
      {Max[# /. {a_, ___}:>If[IntegerQ[a], a, 0]& /@ #]}& /@ 
        #& /@ mList;

    (* Creates a list of the maximum powers of T, such *)
    (* that all the members of the list are of the form *)
    (* $a_{\rm max}+b\,m_i+c\,m_j+\dotsb+d\,m_i\,m_j$ *)
    mList = 
      Plus @@ #& /@ 
      #& /@ 
      Table[
        Table[
          Join[mList[[i,j]], 
            mListStructure[[i,j]]
          ], 
          {j, Length[mList[[i]] ]}
        ], 
      {i, numberOfEquations}
    ];

    (* For the purpose of the initial combinatorics, we must *)
    (* pad lists of only one element. *)
    mList = 
      Table[
        If[Length[ mList[[i]] ]===1,
          PadRight[mList[[i]], 2],
          mList[[i]] ],
        {i, numberOfEquations}
      ];

    (* A little delayed equal to simplify the below expression. *)
    perm := Permutations[Range[Length[mList[[j]] ] ] ];

    (* Combines the expressions for the powers of T in order to *)
    (* find potential balances to the system. *)
    comboList = 
      Flatten[
        Table[
          Table[
            Partition[
              Flatten[
                Union[
                  Table[
                    Prepend[
                      Sort[
                        Drop[perm[[i]], -Length[ perm[[1]] ] + k]
                      ], 
                      j
                    ],
                    {i, 1, Length[perm]}
                  ]
                ]
              ], 
              k+1
            ], 
            {k, 2, Length[mList[[j]] ]}
          ], 
          {j, numberOfEquations}
        ], 
        2
      ];

    (* Combines the polynomials in $m_i$ and solves for $m_i$ *)
    mRules = 
      Table[
        Union[
          Flatten[
            Table[
              Solve[Equal @@
                Flatten[
                  Table[
                    mList[[comboList[[i, 1]], comboList[[i, k]] ]], 
                    {k, 2, Length[comboList[[i]] ]}
                  ]
                ], 
                m[j]
              ], 
              {i, 1, Length[comboList]}
            ]
          ]
        ], 
        {j, 1, numberOfEquations}
      ];

    (* Prints out a warning if it is taking too long. *)
    If[TimeUsed[]-time > 3,
      Print["Still computing the maximum degree, please wait."]
    ];

    (* Creates a set of rules for combining the *)
    (* above solutions of $m_i$ *)
    comboList2 = 
      Partition[
        Flatten[
          Fold[Table, 
            Array[beta, numberOfEquations],
            Table[{beta[i], Length[mRules[[i]] ]}, 
              {i,numberOfEquations}
            ] 
          ] 
        ], 
        numberOfEquations
      ];

    (* Takes these solutions and uses them to find *)
    (* actual integer solutions to $m_i$ *)
    mSoln = 
      Table[
        Solve[
          Table[Equal @@ 
            mRules[[i, comboList2[[j, i]] ]], 
            {i, numberOfEquations}
          ],  
          Array[m, numberOfEquations]
        ], 
        {j, Length[comboList2]}
      ];

    (* If there is a suer case, it adds it to the computed *)
    (* It also test it to see if it is a valid solution.   *)
   If[(DegreeOfThePolynomial /. {opts} /. Options[DDESpecialSolutions]) =!= {},
      mSoln = 
        Append[mSoln,
          ToExpression[
            StringReplace[
              ToString[DegreeOfThePolynomial /. {opts}],
              {"m" -> "Calculus`DDESpecialSolutions`Private`m"}
            ]
          ]
        ]
      ];

    (* Cleans up the list by removing duplicate *)
    (* and extra braces *)
    mSoln = 
      Union[
        Table[
          Flatten[mSoln[[i]] ], 
          {i, Length[mSoln]}
        ]
      ];

    (* Keeps only the solutions which are numeric. *)
    (* Id est, removes any complex solutions. *)
    mSoln2 = 
      Complement[
        mSoln, 
        Flatten[
          Union[
            Table[
              If[NumericQ[Evaluate[m[j] /. mSoln[[i]] ]],
                mSoln[[i]], 
                Null 
              ],
              {i, Length[mSoln]}, 
              {j, numberOfEquations}
            ]
          ], 
          1
        ]
      ];    

    (* Same as above, but removes all non-integer solutions. *)
    mSoln = 
      Complement[
        mSoln, 
        Flatten[
          Union[
            Table[
              If[IntegerQ[ Evaluate[m[j] /. mSoln[[i]] ]],
                Null, 
                mSoln[[i]] 
              ],
              {i, Length[mSoln]}, 
              {j, numberOfEquations} 
            ]
          ], 
          1
        ]
      ];

    (* Finally, it removes all solutions which are not positive. *)
    mSoln = 
      Complement[mSoln,
        Flatten[Union[
          Table[
            If[Positive[ Evaluate[m[j] /. mSoln[[i]] ]],
              Null,
              mSoln[[i]] 
            ],
            {i, Length[mSoln]}, 
            {j, numberOfEquations}
          ]
        ], 
        1
      ]
    ];  

    (* Sets up a local variable with these solutions. *)
    mSoln0 = mSoln;
 
    (* Pulls off the polynomials in m_i which are the *)
    (* dominant terms. *)
    checkList2=
      Table[
        DeleteCases[
          Union[
            Flatten[
              Table[
                Table[
                  If[
                    Evaluate[mList0[[i,k]] /. mSoln[[j]] ]==
                      Max[mList0[[i]]/.mSoln[[j]]],
                    mList0[[i,k]]
                  ],
                  {k, Length[mList0[[i]]]}
                ],
                {j, Length[mSoln]}
              ]
            ]
          ], 
          Null
        ], 
        {i,numberOfEquations}
      ];

    (* Checks to see if any of the highest powers are *)
    (* based on a term which is based on only one m_i *)
    (* If this is the case, it may self balance. *)
    freeVariable = 
      DeleteCases[
        Flatten[
          Table[
            If[
              Length[
                Cases[checkList2[[i]], 
                  ___Integer+__*m[j]|___Integer+m[j] 
                ] 
              ]>1 && 
              numberOfEquations>1,
              m[j], 
              Null
            ],
            {j, numberOfEquations},
            {i, numberOfEquations}
          ]
        ], 
        Null
      ];

    (* The following code runs only if an inequality   *)
    (* exists and solutions might have been missed.    *)
    (* To find the missing solutions, it does a count- *)
    (* down scheme and then test them to see if any    *)
    (* of them are valid. *)
    If[Length[freeVariable]!=0,
      freeVariableMax =   
        Max[
          Table[freeVariable[[j]] /. mSoln[[i]], 
            {i, Length[mSoln]},
            {j, Length[freeVariable]}
          ] 
        ];
      mSolnFree =    
        Partition[
          Flatten[
            Fold[Table, 
              Table[m[i]->beta[i], {i, numberOfEquations}], 
              Table[{beta[k],1,freeVariableMax},{k,numberOfEquations}]
            ]
          ],
          numberOfEquations
        ];
      mSolnFree =   
        Complement[
          DeleteCases[
            Table[
              If[Plus @@ 
                Flatten[
                  Table[
                    If[
                      Length[
                        Cases[mList0[[i]] /. mSolnFree[[j]], 
                          Max[mList0[[i]] /. mSolnFree[[j]]] 
                        ]
                      ]>=2,
                      1, 
                      0
                    ], 
                    {i, numberOfEquations}
                  ]
                ]>=numberOfEquations,
                mSolnFree[[j]], 
                Null
              ], 
              {j, Length[mSolnFree]}
            ], 
            Null
          ], 
          mSoln
        ]
      ];

    (* Displays message to user if freedom exists. *)
    Do[
      If[
        Length[
          Cases[checkList2[[i]], 
            ___Integer+__*m[j]|___Integer+m[j] 
          ] 
        ]>1 && 
        numberOfEquations>1,
        Message[DDESpecialSolutionsmSolver::freedom, 
          Cases[checkList2[[i]],
            ___Integer+__*m[j]|___Integer+m[j] 
          ], 
          i
        ] 
      ],
      {j, numberOfEquations},
      {i, numberOfEquations}
    ];
    If[Length[mSolnFree]!=0,
       mSoln = 
         Join[mSoln, mSolnFree]
    ];
  
  (* The below function takes advantage of the tracking variables. *)
  (* Removes false solutions from mSoln, by checking balances *)
  (* of unique terms. *)
  mSoln = 
    DeleteCases[
      Table[
        If[Plus @@ Flatten[
          Table[
            If[
              Length[
                Cases[#,
                  Max[#]
                ]&[
                  Table[
                    Exponent[
                      Coefficient[
                        Expand[eqnList0[[i]] ], 
                        myTrackingVariable[k]] /. mSoln[[j]], 
                        T
                      ], 
                    {k,1,myTrackingVariableMax}
                  ]
                ]
              ]>=2, 
              1, 
              0
            ], 
            {i, numberOfEquations}
          ]
          ]>=numberOfEquations, 
          mSoln[[j]], 
          Null 
        ], 
        {j, Length[mSoln]}
      ], 
      Null
    ];

    (* If it doesn't find any find any solutions, it quits. *)
    If[Length[mSoln] == 0, 
      Message[DDESpecialSolutionsmSolver::fail]; 
      Abort[ ]
    ];

    (* Appends the maximum value of m_i. *)
    mSoln = 
      Table[
        Join[mSoln[[j]], 
          Table[max[i]->(Max[mList0[[i]] /. mSoln[[j]] ]), 
            {i, numberOfEquations}
          ]
        ],
        {j, Length[mSoln]}
      ];

    (* Prints out a warning if it's taking too long. *)
    If[(TimeUsed[]-time > 3) && !VerboseTest,
      Print["Still computing the maximum degree, please wait."]
    ];

    (* Returns the solutions. *)
    Return[mSoln];
];

(* ************************************************************************ *)

(* : Title : DDESpecialSolutionsBuildSystem.
*  : Author : Douglas Baldwin
*  : Date : 05-24-01 *)

DDESpecialSolutionsBuildSystem[mSoln_List, system_List, vars_List, 
    param_List, opts___?OptionQ]:=
  Block[{numberOfEquations,
         uRules,
         newSystem,
         waveparameters,
         unknowns,
         nonzeros,
         maxT,
         time = TimeUsed[],
         myTemp}, (* Protects Local Variables. *)

    (* Sets a local variable to the number of equations given by user. *)
    numberOfEquations = Length[system];

    (* Converts the results of mSolve to an expression in T *)
    uRules =  mSoln /.
      (m[i_]->j_):>
         (u[i][vars[[1]]+p_Integer:0] :>
            Function[{F},
              Sum[a[i,k]*((F+Tanh[p*c[1]])/(1+F*Tanh[p*c[1]]))^k,
                {k, 0, j}
              ]
            ]
         );

    (* Applies the expressions in T to the system and removes the *)
    (* tracking variables. *)
    newSystem = 
      Expand[system /. Append[#, myTrackingVariable[_]->1]]& /@ uRules;

    (* Clears the denominator to simplify the system. *)
    newSystem = 
      Map[Together[#*Denominator[Together[#]]]&, newSystem, 2];

    (* Prints out warning, if it is taking too long. *)
    If[TimeUsed[]-time > 3,
      Print["Still building the nonlinear algebraic system, please wait."]
    ];

    newSystem = 
      If[(# /. T->-1) === 0 && (# /. T->1) === 0, 
        Factor[#/(1-T^2)], Factor[#]]& /@ #& /@ newSystem;
    newSystem = 
      If[(# /. T->0) === 0, 
        Factor[#/T], Factor[#]]& /@ #& /@ newSystem;

    newSystem = MapAll[Factor, newSystem]; 

    (* Creates a list with the wave parameters (c[1], c[2]) to be *)
    (* passed to the solver. *)

    waveparameters = {c[2], Tanh[c[1]]};

    (* Creates a list of all the a[i,j]'s to be passed to the solver. *)
    unknowns =
      Table[Table[a[i,j], {j, 0, m[i] /. #}], {i, numberOfEquations}]& /@
      mSoln;

    (* Creates a list of those variables which must be nonzero, so as *)
    (* to simplify the work of the solver. *)
    nonzeros = Join[param, Last /@ #, waveparameters]& /@ unknowns;

    (* Flattens the sublists and reorders them to speed up the solver. *)
    unknowns = Reverse[Flatten[#]]& /@ unknowns;

    (* Expands the system. *)
    newSystem = MapAll[Expand,newSystem];

    (* Determines the maximum exponent of T in each of the cases. *)
    maxT = Map[Exponent[#,T]&, newSystem];

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

    (* Removes Integers and other nonzeros (i.e., Tanh[c[1]]). *)
    newSystem = 
      Map[(Times @@ Replace[If[Head[#] === Times, List @@ #, {#}],
        {_Integer :> 1, Tanh[_]:>1, Tanh[_]^_:>1}, 1])&,
        newSystem,
        3];

    (* Converts from expressions to equations. *)
    newSystem = (# == 0)& /@ Flatten[#]& /@ newSystem;

    (* Combines into lists containing {newSystem, unknowns, *)
    (* waveparameters, param, nonzeros} for the solver. *)
    Return[
      MapAll[Factor, 
       Transpose[
        {newSystem, 
          unknowns, 
          Table[waveparameters, {Length[newSystem]}],
          Table[param, {Length[newSystem]}],
          nonzeros
        }
      ]
     ]
    ]
  ];

(* ************************************************************************ *)

(* : Title : DDESpecialSolutionsBuildSolutions *)
(* : Author : Douglas Baldwin *)
(* : Summary : Builds (includes massive simplification) *)
(*   and, if requested, also tests the final solutions. *)

DDESpecialSolutionsBuildSolutions[solution_, mSoln_, 
   eqns_, funcs_, vars_, param_, opts___] :=
   Block[{solutionRules, (* Local version of solution*)
         MySimplificationRules, (* Simplification rules *)
         VerboseTest = Verbose /. {opts} /. Options[DDESpecialSolutions],
         numericTestSolutions, (* numeric test solns *)
         symbolicTestSolutions, (* symbolic test solutions *)
         soln = {}, (* Holds the solutions. *)
         time = TimeUsed[], (* Time tester. *)
         warn = {} (* Collects a list of warning from simplifying *)
        }, (* Protected Local Variables. *)

    (* Sets up a local version to modify *)
    solutionRules = MapAll[Factor, solution]; 

    (* Builds the solutions from the above rules and *)
    (* the powers of T listed in the passed mSoln. *)
    solutionRules = DeleteCases[
      DeleteCases[
        Table[
          Table[
            Join[(mSoln[[jj]] /. (m[i_]->j_):>
              (funcs[[i]] -> 
                Sum[a[i,k]*Tanh[c[1]*vars[[1]]+c[2]*vars[[2]]+phase]^k, 
                  {k, 0, j}])) //. 
                  solutionRules[[jj, ii]],
              (# -> (# /. solutionRules[[jj,ii]]))& /@ param
            ],
            {ii, Length[solutionRules[[jj]]]}],
        {jj, Length[mSoln]}],
        max[_]->_,
        Infinity
      ],
      Rule[a_,b_] /; a == b && FreeQ[a, Alternatives @@ funcs],
      Infinity];

    (* Simplification Rules for reducing the solution *)
    (* even further . . . so as to find more general  *)
    (* solutions. *)
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
          )
      };
 
    (* Applies the above rules to the solutions. *)
    solutionRules = 
      FixedPoint[
        MapAll[Simplify,
          MapAll[Factor, 
            # //. MySimplificationRules
          ] //. MySimplificationRules
        ]&,
        solutionRules,
        3
      ];

     (* Prints out a warning, if things are taking too long. *)
     If[TimeUsed[] - time > 3,
       Print["Still building the solutions, please wait."]
     ];

     (* Depending on the test option, we either proceed with *)
     (* testing of solutions, or we don't. *)
     If[ ( !(NumericTest /. {opts} /. Options[DDESpecialSolutions]) && 
           !(SymbolicTest /. {opts} /. Options[DDESpecialSolutions]) ),
      CellPrint[
        Cell[
          "These solutions are not being tested numerically or " <>
          "symbolically.  To test the solutions set either the " <>
          "NumericTest option to True, or set the SymbolicTest " <>
          "option to True, or both. ",         
          "Message"
        ]
      ];

      If[Length[warn]>0,
        CellPrint[
          Cell[
            "The following simplification rules are being used: " <>
            ToString[Union[warn]],
            "Message"
          ]
        ]
      ];

      Return[
        Map[Union,
          MapAll[Factor,
            MapAll[Expand,
              solutionRules
            ]
          ], 2
        ]
      ]
    ];

    (* Prints the un-tested solution to the user. *)
    If[VerboseTest,
      Print["The possible solutions (before any testing) are: "];
      Print[DDESpecialSolutionsCleanUp[solutionRules]]
    ];

    (* Converts to a pure function. *)
    toPure = 
      (# /. (a__[var__]->temp__):> (a:>Function[{var}, temp]))&;

    (* If Statement for the numeric test option. *)
    If[NumericTest /. {opts} /. Options[DDESpecialSolutions],
      (* Sends message to user. *)
      If[!(VerboseTest /. {opts} /. Options[DDESpecialSolutions]),
        Print["Numerically testing the solutions."]
      ];

      (* Tests to make sure the above solutions are valid. *)
      numericTestSolutions =
        {(eqns /. (a__==b__):>(a-b)) //. toPure[MapAll[TrigToExp, #]], #}& /@ 
          #& /@ solutionRules;

      (* Tests the solutions by replacing all the symbols with *)
      (* random numbers 13 separate times. *)
      (* If one of these tests gives a value less than 10^(-10) the solution *)
      (* will be accepted *)
      numericTestSolutions =
       {Plus @@
        (Table[
           (* Prints out a warning, if things are taking too long. *)
           If[TimeUsed[] - time > 2,
             time = TimeUsed[];
             Print["Still numerically testing the solutions, please wait."]
           ];
           And @@
             (
               (
                 Abs[# /.
                   {a[_,_]->Random[],
                    Sequence @@ ((# -> Random[])& /@ param)
                   }
                 ] < 10^(-10)
               )& /@
               MapAll[ Expand,
                 #[[1]] /.
                   (Append[
                    (# -> Random[])& /@
                      Join[vars, Array[c, Length[vars]] ],
                    phase->0
                    ]
                   )
               ]
             ),
            {13}
          ] /. {True->1, False->0}
        ),
        #
       }& /@ #& /@ numericTestSolutions;

      (* If it works for any of the 13 tests, it keeps it. *)
      (* This works out to be about a 0.0001 chance of missing *)
      (* a correct solution. *)
      soln =
        Cases[numericTestSolutions,
          {a_Integer/;a>0, _List},
          Infinity
        ] //. {_Integer, a_List}:>{a[[2]]};
    ]; (* End of numeric test if statement. *)

    (* The symbolic testing if statement. *)

    (* If Statement for the symbolic test option. *)
    If[SymbolicTest /. {opts} /. Options[DDESpecialSolutions],
      (* Sends message to user. *)
      If[!(VerboseTest /. {opts} /. Options[DDESpecialSolutions]),
        Print["Symbolically testing the solutions."]
      ];

      (* This sets up the input for the next block of code. *)
      (* In that , it takes the equations given by the user, *)
      (* and replaces the user defined functions (e.g. u[n,t]) *)
      (* with the functions found with in the algorithm.  To replace *)
      (* the partial derivatives correctly, we must first convert *)
      (* the solutions to pure functions. *)
      symbolicTestSolutions = 
        {(eqns /. (a__==b__):>a-b) /. toPure[MapAll[TrigToExp, #]], #}& /@
          #& /@ solutionRules;

      (* Attempts to simplify the expressions as much as possible. *)
      symbolicTestSolutions = 
        ExpToTrig[
          FixedPoint[
            MapAll[Factor,
              MapAll[Expand, #] /. MySimplificationRules
            ] /. MySimplificationRules &, 
            #
         ]&  /@ symbolicTestSolutions
       ];

      (* Pulls off the solutions which simplify to zero, and adds *)
      (* them to solns (the final output applies an union, so *)
      (* duplicate solutions are not an issue at this point. *)
      soln = 
        Join[soln,
          Cases[symbolicTestSolutions,
            {{(0)..}, _List},
            Infinity
          ] //. {{(0)..}, a_List}:>{a}
        ];

      (* Removes all the good cases, so we may output the bad *)
      (* cases to the user.*)
      symbolicTestSolutions = 
        DeleteCases[
          DeleteCases[symbolicTestSolutions,
            {{(0)..}, _List},
            Infinity
         ],
         {}
       ];

      If[(Map[Union, symbolicTestSolutions, 3] //. {{}}->{}) != {},
        (* Sends out the left over (questionable) solutions to *)
        (* the user for hand/assisted inspection *)
        CellPrint[
          Cell[
            "These solutions did not easily simplify to zero. " <>
            "Please test these equations by hand or interactively " <>
            "with Mathematica. ",
            "Message"
          ]
       ];
       Print[DDESpecialSolutionsCleanUp[#]]& /@ symbolicTestSolutions;
     ];
   ];

   (* Prints simplification rules to the screen *)
   If[Length[warn]>0,
     CellPrint[
       Cell[
         "The following simplification rules are being used " <>
         "to test the solutions: " <>
         ToString[Union[warn]],
         "Message"
       ]
    ]
  ];

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
];

(* ************************************************************************ *)

(* : Title : DDESpecialSolutionsCleanUp *)
(* : Author : Douglas Baldwin *)
(* : Summary : Remove "DDESpecialSolutionsPrivate`" from output. *)

DDESpecialSolutionsCleanUp = 
   ToExpression[
     StringReplace[ToString[InputForm[#]],
       "Calculus`DDESpecialSolutions`Private`"->""
     ]
   ]&

End[] (* `Private` context *)

SetAttributes[DDESpecialSolutions, ReadProtected]

EndPackage[]

(* ************************************************************************ *)

(* Nonlinear algebraic solver by Unal Goktas and Willy Hereman. *)
(* Written by Unal Goktas (WRI) October/November 2000 *)

BeginPackage["Algebra`AnalyzeAndSolve`"]

Unprotect[AnalyzeAndSolve]

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
      ]
]

AnalyzeAndSolve[system: {HoldPattern[_ == _]..}, primaryunknowns_,
   secondaryunknowns_, parameters_, nonzeros_] :=
   AnalyzeAndSolve[(#[[1]]-#[[2]]&) /@ system, primaryunknowns,
      secondaryunknowns, parameters, nonzeros]

AnalyzeAndSolve[system_, primaryunknowns_, secondaryunknowns_, {},nonzeros_]:=
   Block[{constraints},
      constraints = (And @@ ((# != 0 &) /@ nonzeros));
      Internal`DeactivateMessages[
         Solve[(And @@ ((# == 0 &) /@ system)) && constraints,
            Join[primaryunknowns, secondaryunknowns], Sort -> False],
         Solve::svars
      ]
   ]

(* ************************************************************************ *)

(* "system" is polynomial in "primaryunknowns", "secondaryunknowns", and 
"parameters". *)
AnalyzeAndSolve[system_, primaryunknowns_, secondaryunknowns_, parameters_,
   nonzeros_] :=
   Block[{a, globalsol = {}, constraints},
      a = Together[({#}& /@ system) /. {{}}];
      constraints = (And @@ ((# != 0 &) /@ nonzeros));
      MapThread[
         RecursivelyKeepTrack[#1, #2, primaryunknowns, secondaryunknowns,
            parameters, nonzeros, constraints]&, {a, {{}}}];
      Union[globalsol]
   ]

(* ************************************************************************ *)

(* RecursivelyKeepTrack[{}, __] := {} *)

RecursivelyKeepTrack[{}, sol_, __] := (AppendTo[globalsol, sol]; {})

RecursivelyKeepTrack[system_, sol_, __] /;
   (!FreeQ[system, DirectedInfinity] || !FreeQ[system, Indeterminate]) := {}

RecursivelyKeepTrack[system_, sol_, primaryunknowns_, secondaryunknowns_,
   parameters_, nonzeros_, constraints_] :=
   Block[{a, b, c},
      a = FactorListAndCleanUp[#, primaryunknowns, secondaryunknowns,
             parameters, nonzeros]& /@ system;
      a = Union[a];
      a = Sort[a, (ComplexityLevel[#1, primaryunknowns, secondaryunknowns,
                      parameters] <=
                   ComplexityLevel[#2, primaryunknowns, secondaryunknowns,
                      parameters]&)];
      b = a[[1]];
      b = SolveStepByStep[#, primaryunknowns, secondaryunknowns, parameters,
             constraints /. sol, sol]& /@ b;
      b = (Sequence @@ # &) /@ b;
      If[Length[b] == 0, Return[{}]];
      b = Transpose[b];
      c = (constraints && (And @@ #))& /@ b[[2]];
      b = b[[1]];
      a = Together[
             Internal`DeactivateMessages[Rest[a] /. b,
                Power::infy, General::indet
             ]
          ];
      a = Numerator[a];
      a = DeleteCases[a, {___, 0, ___}, {2}];
      MapThread[
         RecursivelyKeepTrack[#1, #2, primaryunknowns, secondaryunknowns,
            parameters, nonzeros, #3]&, {a, b, c}]
   ]

(* ************************************************************************ *)

FactorListAndCleanUp[system_, primaryunknowns_, secondaryunknowns_, 
                     parameters_, nonzeros_] :=
   Block[{a},
      a = Flatten[Map[First[#]&, FactorList /@ system, {2}]];
      a = DeleteCases[a, _?(NumericQ[#] || MemberQ[nonzeros, #]&)];
      Union[a]
   ]

(* ************************************************************************ *)

ComplexityLevel[expr_List, primaryunknowns_,secondaryunknowns_,parameters_]:=
   Max[ComplexityLevel[#, primaryunknowns, secondaryunknowns, parameters]& /@
      expr]

ComplexityLevel[expr_, primaryunknowns_, secondaryunknowns_, parameters_] :=
   Block[{a, b},
      a = Union[Cases[{expr}, q_ /; MemberQ[primaryunknowns, q], -1]];
      b = Length[a];
      (
       SubComplexityLevel[expr, a, b, 1]
      ) /; b != 0
   ]

(* ************************************************************************ *)

ComplexityLevel[expr_, primaryunknowns_, secondaryunknowns_, parameters_] :=
   Block[{a, b},
      a = Union[Cases[{expr}, q_ /; MemberQ[secondaryunknowns, q], -1]];
      b = Length[a];
      (
       SubComplexityLevel[expr, a, b, 2] 
      ) /; b != 0
   ]

(* ************************************************************************ *)

ComplexityLevel[expr_, primaryunknowns_, secondaryunknowns_, parameters_] :=
   Block[{a, b},
      a = Union[Cases[{expr}, q_ /; MemberQ[parameters, q], -1]];
      b = Length[a];
      (
       SubComplexityLevel[expr, a, b, 3] 
      ) /; b != 0
   ]

(* ************************************************************************ *)

SubComplexityLevel[expr_, a_, b_, level_] :=
   Block[{c = Select[a, PolynomialQ[expr, #]&]},
      Which[
         Length[c] == 0,
         100*b*level+LeafCount[expr],
         True,
         Min[Exponent[expr, c]]
      ]
   ]

(* ************************************************************************ *)

(* solves a single equation *)

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
   ]

(* ************************************************************************ *)

SolveStepByStep[eqn_, primaryunknowns_, secondaryunknowns_, parameters_,
   constraints_, sol_] :=
   Block[{a},
      a = Union[Cases[{eqn}, q_ /; MemberQ[secondaryunknowns, q], -1]];
      (
       SubSolveStepByStep[eqn, a, parameters, constraints, sol]
      ) /; Length[a] != 0
   ]

(* ************************************************************************ *)

SolveStepByStep[eqn_, primaryunknowns_, secondaryunknowns_, parameters_,
   constraints_, sol_] :=
   Block[{a},
      a = Union[Cases[{eqn}, q_ /; MemberQ[parameters, q], -1]];
      (
       SubSolveStepByStep[eqn, a, {}, constraints, sol]
      ) /; Length[a] != 0
   ]

(* ************************************************************************ *)

SolveStepByStep[___] := {}

SubSolveStepByStep[eqn_, primaryunknowns_, pars_, constraints_, sol_] :=
   Block[{a, b, c},
      a = Select[primaryunknowns, PolynomialQ[eqn, #]&];
      If[Length[a] != 0,
         a = Sort[a, Exponent[eqn, #1] <= Exponent[eqn, #2]&];
         a = Flatten[{a, Complement[primaryunknowns, a]}],
         a = primaryunknowns
      ];
      c = Reduce[eqn == 0 && constraints, Flatten[{a, pars}], Sort -> False];
      a = {ToRules[c]};
      If[Length[a] == 0, Return[{}]];
      c = Cases[{#}, p_ != q_, -1]& /@ If[Head[c] === Or, List @@ c, {c}];
      b = Internal`DeactivateMessages[sol /. a, Power::infy, General::indet];
      Union[Transpose[{Flatten /@ Thread[{b, a}, List, 2], c}]]
   ]

(* ************************************************************************ *)

End[] (* `Private` context *)

SetAttributes[AnalyzeAndSolve, ReadProtected]

EndPackage[]

Print["Package DDESpecialSolutions.m was succesfully loaded."];

(* ************************************************************************ *)
