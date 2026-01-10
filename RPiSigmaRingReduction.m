(* ::Package:: *)

$activateEcho=False;
Clear[JEcho];
JEcho[args___]:=If[$activateEcho,Echo[args],args]


Clear[RationalReduction]
RationalReduction[g_,f_,tower_]:=Module[{xi,eta},
{xi,eta}=NormalForm[f,tower];

Return[eta^(-1) RationalReductionSigmaReduced[eta g,xi,tower]]
]


Clear[RationalReductionSigmaReduced]
RationalReductionSigmaReduced[g_,xi_,tower_]:=Module[{gT,h},
{h,gT}=ProperAndPolynomialParts[f,var];
s

]


Clear[NormalForm]
NormalForm[f_,tower_]:=Module[{xi,eta,},


Return[{xi,eta}]
]


(* ::Subsection:: *)
(*Rational*)


(* ::Input::Initialization:: *)
Clear[ProperAndPolynomialParts];
ProperAndPolynomialParts[f_,var_Symbol]:=Module[{ff,num,den,r,pp,fp},
ff=Together[f];
{num,den}=NumeratorDenominator[ff];
{pp,r}=PolynomialQuotientRemainder[num,den,var];
Return[{r/den,pp}]
];
