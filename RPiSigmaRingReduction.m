(* ::Package:: *)

 


Clear[RationalReduction]
RationalReduction[g_,f_,tower_]:=Module[{xi,eta},
{xi,eta}=NormalForm[f,tower];

Return[eta^(-1) RationalReductionSigmaReduced[eta g,xi,tower]]
]


Clear[RationalReductionSigmaReduced]
RationalReductionSigmaReduced[g_,xi_,tower_]:=Module[{},

s

]


Clear[NormalForm]
NormalForm[f_,tower_]:=Module[{xi,eta},


Return[{xi,eta}]
]
