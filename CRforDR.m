(* ::Package:: *)

(* ::Text:: *)
(*Copyright (C) 2026 Jakob Obrovsky*)
(**)
(*This file is part of CRforDR.*)
(**)
(*CRforDR is free software: you can redistribute it and/or modify it under the terms of the GNU Lesser General Public License (LGPL) as published by the Free Software Foundation; either version 3 of the License, or  (at your option) any later version.  See https://www.gnu.org/licenses/*)


Get["CRforDR/RationalReduction.m"]


(* ::Input::Initialization:: *)
BeginPackage["CRforDR`"];
ClearAll@@Names["CRforDR`*"];


$CRforDRenableAssert=False;


$VersionCRforDR="Version 0.2.1 (June 11, 2026)";


(* ::Input::Initialization:: *)
CRforDR::usage="TowerInfo must be initialized with ResetTower[tower] before using this function
Call: CRforSimpleDR[g,f,tower] or CRforSimpleDR[g,tower]
where:
	tower: RPiSigma tower (which has been already initialized by calling ResetTower[tower], for details see ?ResetTower
	g: An element in the ring encoded by tower
	f: An invertible element in this ring. f must be f=1 if n>0.
       Can be left out, in this case f is set to 1.
Out: {gS,gR}, with \[CapitalDelta]_f(gS)+gR===g, where gR is a remainder.
Options: \"SimplifyFullOutput\" -> True|False (Default: False) : Whether also gS should be simplified, or only gR, which is the default.";
ResetTower::usage="(Re)Initializes TowerInfo. Call at the beginning and whenever a new tower is used. The given options are used in the function CRforDR.
Call: ResetTower[tower]
where:
	tower: An represented by
	{{x,1,1},{y_1,alpha,0},...,{y_l,alpha_l,0},{p_1,a_1,0},...{p_m,a_m,0},{t_1,1,b_1},{t_2,1,b_2},...{t_n,1,b_n}}
	(l>=0,m>=0,n>=0, where x,y_i,p_i,t_i are the generators and the shift is defined by \[Sigma](p_i)=alpha_i p_i and \[Sigma](t_i)= t_i + b_i
	The y_i must be R-monomials, the p_i \[CapitalPi]-monomials and the t_i \[CapitalSigma]-monimails.

Options: 
\"SingleSetOfRepresentatives\"->True|False|{pol1,pol2,...pol_k} (Default: False) : Whether a single set of Representatives should be used for Rational Reduction. This set can be explicitely given as a list of monic, pairwise shift-coprime polynomials {pol1,pol2,...pol_k}. The default is that an individual set is constructed for each \[CapitalDelta]_f.
\"UseAlwaysIdempotents\"->True|False (Default: False) : Whether Idempotent Representation should be used always or only when the tower is not a simple tower (default)
";
ParametricTelescopingViaCR ::usage="";
MyTogether::usage="Chooses an efficient way to simplify the given object. The output is canonical w.r.t. the R-extension, i.e. it is explicitely 0 if f is equal to zero in the given tower.";
DeltaF::usage="DeltaF[g,f,tower] returns f*MySigma[g,1,tower]-f";
MySigma::usage="MySigma[g,k,tower] returns \[Sigma]^k(g) where \[Sigma] is defined by tower.";
CreativeTelescopingViaCR::usage="CreativeTelescopingViaCR[g,{towerN,towerK}] finds the a recurrence 
\!\(\*SubscriptBox[\(c\), \(0\)]\) g + ... +  \!\(\*SubscriptBox[\(c\), \(m\(\\\ \)\)]\)\!\(\*SubscriptBox[\(\[Sigma]\), \(m\)]\)(g)=\!\(\*SubscriptBox[\(\[CapitalDelta]\), \(k\)]\)(h)
of minimal order m. The output is given as {{\!\(\*SubscriptBox[\(c\), \(0\)]\),...,\!\(\*SubscriptBox[\(c\), \(m\)]\)},h}. h is not simplified by any means. If no recurrence of order OptionValue[\"MaxOrder\"] (default: 30) exists, then the output is {}. 
Options:
\"WithNegativeShifts\" -> True|False (Default: False)
Whether also negative shifts are used internally in the computation. This can make the computation faster.
\"SimplifyFullOutput\" -> True|False (Default: False) : Whether the certificate should be simplified, or only the found recurrenc, which is the default.";


(* ::Input::Initialization:: *)
Begin["`Private`"];


(* ::Input::Initialization:: *)
CellPrint[TextCell["RPiSigmaRingReduction by Yiman Gao and Jakob Obrovsky \[LongDash] \[Copyright] RISC \[LongDash] "<>$VersionCRforDR (*, 
               ButtonBox[StyleBox["Help", "Hyperlink", FontVariations -> {"Underline" -> True}],
					ButtonFunction :> RingReductionHelp[], ButtonEvaluator -> Automatic, ButtonData :> {"", ""}, 
					ButtonFrame -> "None"]*), "Print", CellFrame -> 0.5`, FontColor -> GrayLevel[0.`], 
				Background -> RGBColor[102/256,139/256, 232/256], ButtonBoxOptions -> {Active -> True}]]


(* ::Subsection:: *)
(*Main*)


Clear[CRforDR]
Options[CRforDR]={"SimplifyFullOutput"->False}
CRforDR[g_,tower_?MatrixQ,opts:OptionsPattern[]]:=CRforDR[g,1,tower,opts]
CRforDR[g_,f_,tower_?MatrixQ,opts:OptionsPattern[]]:=
	If[(TowerInfo["UseAlwaysIdempotents"]&&KeyExistsQ[TowerInfo,"R-Extension"])||!SimpleTowerQ[tower],
		IdempotentReduction[g,f,tower,opts]
	,
		CRforSimpleDR[g,f,tower,opts]
	]


(* ::Text:: *)
(*Main scheduler which calls Reduction-function which fits to this simple tower. *)


Clear[CRforSimpleDR];
Options[CRforSimpleDR]={"SimplifyFullOutput"->False}
CRforSimpleDR::malformedTower="Error: Tower `1` is malformed and not fit for CRforSimpleDR w.r.t Delta `2`";
CRforSimpleDR[0,_,_?MatrixQ,OptionsPattern[]]:={0,0}
CRforSimpleDR[g_,tower_?MatrixQ,opts:OptionsPattern[]]:=CRforSimpleDR[g,1,tower,opts];
CRforSimpleDR[g_,f_,tower_?MatrixQ,OptionsPattern[]]:=Module[{gTrans,fTrans,step,found,x,alpha,beta,gS,gR},
MyAssert[Head[TowerInfo]===Association];
Sow[Timing[
If[Length[tower]==1&&tower[[1,2]]===1,
	{x,step}=tower[[1,{1,3}]];
	If[step=!=1,
		gTrans=(g/.x->step x);
		fTrans=MyTogether[(f/.x->step x)];
	,
		{fTrans,gTrans}={f,g};
	];
	If[TowerInfo["SingleSetOfRepresentatives"],
		If[!KeyExistsQ[TowerInfo,x],TowerInfo[x]={}];
		{{gS,gR},TowerInfo[x]}=RationalReduction`RationalReduction[gTrans,fTrans,{{x,1,1}},"Representatives"->TowerInfo[x],"EncodeRNFinRepresentatives"->True];	
		
	,	
		If[!KeyExistsQ[TowerInfo,x],TowerInfo[x]=<||>];
		found=MyLookupPoly[Keys[TowerInfo[x]],fTrans];
		If[Head[found]===Missing,TowerInfo[x][fTrans]={};found=fTrans;];
		{{gS,gR},TowerInfo[x][found]}=RationalReduction`RationalReduction[gTrans,fTrans,{{x,1,1}},"Representatives"->TowerInfo[x][found]];
	];
	If[step=!=1,
		gS=(gS/.x-> x/step);
		gR=MyTogether[gR/.x-> x/step];
	];
	
,
{alpha,beta}=tower[[-1,2;;3]];
If[beta===0,
	If[KeyExistsQ[TowerInfo,"R-Extension"]&&MemberQ[TowerInfo["R-Extension"][[;;,1]],tower[[-1,1]]],
		{gS,gR}=SimpleRReduction[g,f,tower];
	,
		{gS,gR}=PiReduction[g,f,tower];
	];
,If[alpha===1&&f===1,
	{gS,gR}=SigmaRingReduction[g,tower];
,
	Message[CRforSimpleDR::malformedTower,tower,f];
	Abort[];
];]];
][[1]],ToString[tower[[-1,1]]]<>" combined"];
MyAssert[CheckReduction[{g,f},{gS,gR},tower]];
Return[{If[OptionValue["SimplifyFullOutput"],MyTogether[gS],gS],gR}];
]


(* ::Text:: *)
(*Input :  An admissible tower (as specified for function CRforSimpleDR). *)
(*    Output : Null*)
(*    Side effect : If there is no R-extension then*)
(*         TowerInfo=<| |>,*)
(*           otherwise if there is an R - extension {y, alpha, 0} in the tower*)
(*        TowerInfo = <|"R-Extension" -> {y, lambda}|>,  where lambda = ord (alpha)*)


ResetTower::malformedTower="Error: Tower `1` contains more than one R-extension, this is not implemented";
Clear[ResetTower]
Options[ResetTower]={"SingleSetOfRepresentatives"->False,"UseAlwaysIdempotents"->False}

ResetTower[tower_?MatrixQ,OptionsPattern[]]:=Module[{newtower,ordList,orders,yList,RExt,alphas},
	TowerInfo=<||>;
	If[Head[OptionValue["SingleSetOfRepresentatives"]]===List,
		TowerInfo[tower[[1,1]]]={#,"=="}&/@OptionValue["SingleSetOfRepresentatives"];
		TowerInfo["SingleSetOfRepresentatives"]=True;
	,
		TowerInfo["SingleSetOfRepresentatives"]=TrueQ[OptionValue["SingleSetOfRepresentatives"]]
	];
	TowerInfo["UseAlwaysIdempotents"]=OptionValue["UseAlwaysIdempotents"];
	(*If[Length[RExt]>1,Message[ResetTower::malformedTower,tower];Abort[]];*)
	TowerInfo["Generators"]=tower[[;;,1]];
	(*Delete precomputed higher towers*)
	ReleaseHold[MapAt[Unset,Select[DownValues[MyChangeShiftTower],(Head[#[[1,1,1]]]===List && IntegerQ[#[[1,1,2]]])&][[;;,1]],{All,1}]];
	
	newtower=tower;
	While[True,
		RExt=Select[newtower,(#[[3]]===0 && RootOfUnityQ[#[[2]]])&];
		If[Length[RExt]==0,Break[]];
		yList=RExt[[;;,1]];
		orders=(MyGetOrderOfUnity/@RExt[[;;,2]]);
		alphas=Table[RExt[[i,2]]^(Times@@RExt[[;;i-1,2]]),{i,Length[RExt]}];
		MyAssert[Union[MyTogether[Select[tower,MemberQ[yList,#[[1]]]& ][[;;,2]]^orders]][[1]]===1];
		If[!KeyExistsQ[TowerInfo,"R-Extension"],TowerInfo["R-Extension"]={}];
		TowerInfo["R-Extension"]=
			SortBy[Join[TowerInfo["R-Extension"],Transpose[{yList,alphas,orders}]],FirstPosition[tower[[;;,1]],#[[1]]][[1]]&];
		{newtower,ordList}=RemoveRMonomials[newtower,yList,0];
		MyAssert[ordList===orders];
		MyAssert[Length[newtower]+Length[TowerInfo["R-Extension"]]==Length[tower]];
	]

];


(* ::Subsection:: *)
(*Auxiliary Functions*)


(* ::Text:: *)
(*SimpleTowerQ[tower_] returns True if tower is a simple tower and False otherwise. Not defined for malformed tower.*)


Clear[SimpleTowerQ];
SimpleTowerQ[{}]:=True
SimpleTowerQ[{{_,_,_}}]:=True
SimpleTowerQ[tower_?MatrixQ]:=SimpleTowerQ[Most[tower]]&&Length[CoefficientRules[tower[[-1,2]],Join[Prepend[tower[[2;;-2,1]],Unique[]],1/tower[[2;;-2,1]]]]]==1
SimpleTowerQ[_]:=False


Clear[MyAssert]
MyAssert::AssertionFaild="Assertion failed: `1` does not evaluate to true";
Attributes[MyAssert]=HoldAll;
MyAssert[check_]:=If[$CRforDRenableAssert,If[!ReleaseHold[TrueQ[check]],Message[MyAssert::AssertionFaild,Hold[check]];Abort[]]];


Clear[MyLookupPoly];
MyLookupPoly[polList_List,poly_]:=Module[{polother,result,polyMod,repRules},
repRules=Dispatch[Thread[Variables[polList]->RandomInteger[{Floor[Developer`$MaxMachineInteger/12],Developer`$MaxMachineInteger},Length[Variables[polList]]]]];
polyMod=poly/.repRules;
result=Missing[];
Do[
	If[MyTogether[(polother/.repRules)-polyMod]===0,
		If[MyTogether[(poly-polother)]===0,
			result=polother;
			Break[];
		]
	]
,{polother,polList}];
Return[result];

]


(* ::Text:: *)
(*Chooses an efficient way to simplify the given object. The output is canonical w.r.t. the R-extension, i.e. it is explicitely 0 if f is equal to zero in the given tower.*)
(*Nothing for QQ,*)
(*plain MyTogether for QQ (x_ 1, x_ 2, ...),*)
(*MyEliminateRootObjects for algebraic numbers *)
(* (Mathematica is really bad at dealing with algebraic numbers like (-1)^(2/3))*)


Clear[MyTogether]
Attributes[MyTogether]={Listable}
MyTogether[f_]:=
If[Variables[f]==={},
MyEliminateRootObjects[f]
,If[KeyExistsQ[TowerInfo,"R-Extension"],
   With[{yL=TowerInfo["R-Extension"][[;;,1]],l=TowerInfo["R-Extension"][[;;,-1]]},
	If[(Intersection[Variables[f],yL]=!={})(*&&Exponent[f,y]>=l*),
		With[{prel=Together[MyEliminateRootObjects[(Collect[f,yL]/.Thread[yL^(AAA121212_)->yL^Mod[AAA121212,l]])],Extension->Automatic]},
		If[Intersection[Variables[Denominator[prel]],yL]=!={},
			Together[Sum[e[l,expon133,yL](prel/.Thread[yL->((-1)^(l/2))^expon133]),{expon133,Flatten[Array[List,l],Length[l]-1]-1}]]
			(*Together[MyEliminateRootObjects[(Collect[Numerator[prel],yL]/.Thread[yL^(AAA121212_)->yL^Mod[AAA121212,l]])],Extension->Automatic]/Denominator[prel]*)
		,
			prel
		]
		]
,
	Together[MyEliminateRootObjects[f],Extension->Automatic]
	]]
,
	Together[MyEliminateRootObjects[f],Extension->Automatic]
]
]



(*Clear[MyTogether]
Attributes[MyTogether]={Listable}
MyTogether[f_]:=
If[Length[Variables[f]]==0,
MyEliminateRootObjects[f]
,If[KeyExistsQ[TowerInfo,"R-Extension"],
   With[{yL=TowerInfo["R-Extension"][[;;,1]],l=TowerInfo["R-Extension"][[;;,-1]]},
	If[(Intersection[Variables[f],yL]=!={})(*&&Exponent[f,y]>=l*),
		If[PolynomialQ[f,yL],
		With[{first=Collect[MyEliminateRootObjects[f],Reverse[Rest[TowerInfo["Generators"]]]]/.Thread[yL^(AAA121212_)->yL^Mod[AAA121212,l]]},
		If[And@@Thread[Exponent[first,yL]<l],first,Collect[first,Reverse[Rest[TowerInfo["Generators"]]],Together[#,Extension->Automatic]&]]
		
		With[{prel=Together[MyEliminateRootObjects[(Collect[f,yL]/.Thread[yL^(AAA121212_)->yL^Mod[AAA121212,l]])],Extension->Automatic]},
		If[Intersection[Variables[Denominator[prel]],yL]=!={},
			Together[MyEliminateRootObjects[(Collect[Numerator[prel],yL]/.Thread[yL^(AAA121212_)->yL^Mod[AAA121212,l]])],Extension->Automatic]/Denominator[prel]
		,
			prel
		]
		]
,
	Collect[MyEliminateRootObjects[f],Reverse[Rest[TowerInfo["Generators"]]],Together[#,Extension->Automatic]&]
	]]
,
	Collect[MyEliminateRootObjects[f],Reverse[Rest[TowerInfo["Generators"]]],Together[#,Extension->Automatic]&]
]
]*)


Clear[MyChangeShiftTower];
MyChangeShiftTower[tower_List,1]:=tower
MyChangeShiftTower[tower_List,k_]/;(k<-1):=MyChangeShiftTower[tower,k]=MyChangeShiftTower[MyChangeShiftTower[tower,-1],-k]
MyChangeShiftTower[tower_List,k_]/;(k> 1):=MyChangeShiftTower[tower,k]=Module[{resminus,resbare},
	resminus=MyChangeShiftTower[tower,k-1];
	resbare=MySigma[tower[[;;,2]]tower[[;;,1]]+tower[[;;,3]],resminus];
	Return[Table[{tower[[i,1]],MyTogether@Coefficient[resbare[[i]],tower[[i,1]]],MyTogether@Coefficient[resbare[[i]],tower[[i,1]],0]},{i,Length[tower]}]];
]
MyChangeShiftTower[{},_]:={}
MyChangeShiftTower[tower_List,-1]:=MyChangeShiftTower[tower,-1]=Module[{trunktower=MyChangeShiftTower[tower[[;;-2]],-1],t,alpha,beta},
	{t,alpha,beta}=tower[[-1]];
	Return[Append[trunktower,{t,MyTogether@MySigma[1/alpha,trunktower],MyTogether@MySigma[-beta,trunktower]}]]
]



Clear[MySigma]
MySigma[expr_,0,___]:=expr
MySigma[expr_,rest__]:=If[Variables[expr]==={},expr,Sigma`DifferenceFields`BasicTools`DFInterface`TSigma[expr,rest,False]]/.Sigma`Algebra`CompAlgSigma`II->I;


Clear[MySigma]
MySigma[expr_,0,___]:=expr
MySigma[expr_,tower_]:=expr/.Thread[tower[[;;,1]]->tower[[;;,2]]tower[[;;,1]]+tower[[;;,3]]]
MySigma[expr_,1,tower_]:=expr/.Thread[tower[[;;,1]]->tower[[;;,2]]tower[[;;,1]]+tower[[;;,3]]]
MySigma[expr_,k_,tower_]:=MySigma[expr,1,MyChangeShiftTower[tower,k]]; 


Clear[DeltaF];
DeltaF[g_,f_,tower_?MatrixQ]:=f MySigma[g,1,tower]-g


(* ::Subsection::Closed:: *)
(*Re-used*)


$activateEcho=False;
Clear[myEcho];
myEcho[args___]:=If[$activateEcho,Echo[args]];


Clear[MyEliminateRootObjects];
Attributes[MyEliminateRootObjects]={Listable};
MyEliminateRootObjects[f_]:=If[FreeQ[f,Power[_,Rational[_,_]]|Root[__]],f,ToRadicals[RootReduce[Together[f]]]]


Clear[MatrixRankHeuristic]
MatrixRankHeuristic[matIn_]:=Module[{matMod,repRules},
repRules=Thread[Variables[matIn]->RandomInteger[{Floor[Developer`$MaxMachineInteger/12],Developer`$MaxMachineInteger},Length[Variables[matIn]]]];
matMod=matIn/.Dispatch[repRules];
If[ArrayQ[matMod,_,IntegerQ],
	Return[MatrixRank[matMod,Modulus->NextPrime[RandomInteger[{Floor[Developer`$MaxMachineInteger/12],Developer`$MaxMachineInteger}],-1]]]
,
	Return[MatrixRank[matMod]]
]
]


(* ::Subsection::Closed:: *)
(*Sigma*)


(* ::Text:: *)
(*Input/Output: See function SigmaRingReduction. *)
(*Note: Combines the functionality of AuxiliaryReduction and MyProjection. *)
(*For using those functions, the line "Return[AuxiliaryProjectionReduction[pp,tower]];" has to be commented out in SigmaReduction*)


Clear[AuxiliaryProjectionReduction]
AuxiliaryProjectionReduction[0,_?MatrixQ]:={0,0}
AuxiliaryProjectionReduction[p_,tower_?MatrixQ]:=Module[{betaS,betaR,w,ct,b,c,t,d,pCoeffs,beta,q,r,lc,g,u,tower1,sub},
{t,beta}=tower[[-1,{1,3}]];
{q,r}={0,0};
tower1=Drop[tower,-1];
{betaS,betaR,b,c}= TowerInfo[t][[;;4]];
MyAssert[CheckReduction[{beta,1},{betaS,betaR},tower]];

pCoeffs=CoefficientList[p,t];
Do[
	If[pCoeffs[[+1+d]]===0,Continue[]];
	{g,u}=CRforSimpleDR[pCoeffs[[+1+d]],tower1];
	If[g===0 && u===0,Continue[]];
	ct=Rational`MyCoefficientNew[tower[[;;,1]],u,b];
	w=MyTogether[ct/c];
	{q,r}+= {w/(d+1) t^(d+1)+(g-w betaS)*t^d,MyTogether[u-w*betaR]t^d};
	
	MyAssert[Rational`MyCoefficientNew[tower[[;;,1]],u-w*betaR,b]===0];
	sub=If[Length[tower]>1,Collect[MySigma[g-w betaS,tower1],tower[[-2,1]],MyTogether],MyTogether[MySigma[g-w betaS,tower1]]];
	pCoeffs[[;;d]]-=sub Table[Binomial[d,i] beta^(d-i),{i,0,d-1}];
	pCoeffs[[;;d]]-=Table[w/(d+1) Binomial[d+1,i] beta^(d+1-i),{i,0,d-1}];
	
,{d,Length[pCoeffs]-1,0,-1}];
(*r=Sum[pCoeffs[[i]]t^(i-1),{i,Length[pCoeffs]}];*)
Return[{q,r}];
];


(* ::Text:: *)
(*Input: A tower as required by function CRforSimpleDR, where the last extension is a Sigma extension {t,1,beta}*)
(*        g, an element in the tower (not necessarily simplified or canonocalized)*)
(*  Output: {gS,gR}, two elements in the tower s.t.*)
(*             g=\[CapitalDelta](gS)+gR*)
(*          is a complete reduction of g. gR is simplified (in particular gR === 0 if gR can be simplified to zero)*)


SigmaRingReduction[0,_]:={0,0}
SigmaRingReduction[g_,tower_?MatrixQ]:=Module[{t=tower[[-1,1]],pp=g,q,r,b,c,u=0,v},
MyAssert[tower[[-1,2]]===1];

If[Length[tower]===1,Return[CompleteReduction0[f,t]]];(* <-- this is curently not used*)
(*{fp,pp}=Rational`ProperAndPolynomialParts[f,t];
{g,h}=NormalReduction[fp,tower];*)
(*pp=Collect[f,t,MyTogether];*)
If[!KeyExistsQ[TowerInfo,t],Sow[Timing[TowerPrecomp[tower]][[1]],"TowerPrecomp"]];


Return[AuxiliaryProjectionReduction[pp,tower]];


{q,r}=AuxiliaryReduction[pp,tower];
If[r===0, Return[{q,r}]];
{b,c}= TowerInfo[t][[3;;4]];
Sow[Timing[
{u,v}=MyProjection[r,b,c,tower];
][[1]],"MyProjection"];
{MyTogether[q+u],v}

];



(* ::Text:: *)
(*Input : A tower where the last extension is a Sigma extension {t, 1, beta}*)
(*	    TowerInfo must be initialized .*)
(*Output : Null*)
(*Side effect : TowerInfo[t] is set to [ l_t, \[Phi] (b_i), \[CapitalTheta] (t), B_t]*)
(*	where *)
(*	     \[Phi] (b_i), the remainder of beta in the previous tower,*)
(*	    l_i, an element in the previous tower s . t . b_i = \[CapitalDelta] (l_t) + \[Phi] (b_i)*)
(*		\[CapitalTheta] (t), a basis element effective in \[Phi] (b_i)*)
(*	    B_t, a basis of the intersection up to certain level*)


TowerPrecomp::constantsExtended="Error: `1` is not a Sigma-extension of tower `2`";
Clear[TowerPrecomp];
TowerPrecomp[tower_?MatrixQ]:=Module[{t,beta,g,r,b,c,B},
{t,beta}=tower[[-1,{1,3}]];
MyAssert[!KeyExistsQ[TowerInfo,t]];
{g,r}=CRforSimpleDR[beta,tower[[;;-2]]];
If[r===0,Message[TowerPrecomp::constantsExtended,tower[[-1]],tower[[;;-2]]];Abort[]];
{b,c}=Rational`BasisElement[tower[[1;;-2,1]],r];
B={{{-g,1},{r}}};
TowerInfo[t]={MyTogether[g],r,b,c,B};
]


Clear[CheckReduction]
CheckReduction[{g_,f_},{gS_,gR_},tower_]:=(MyTogether[DeltaF[gS,f,tower]+gR-g]===0)


(* ::Text:: *)
(*Input :  A tower as required by function CRforSimpleDR, where the last extension is a Sigma extension t*)
(*         r, an element of the auxiliary space,*)
(*         b, an element in the C - basis effective in \[Phi] (\[CapitalDelta] (t)),*)
(*        c, equal to b^*\circ\[Phi] (t');*)
(*  Output : {u, v}, u in K[t] and v in the b - complement such that r = \[CapitalDelta] (u) + v*)


(*not used*)
MyProjection[0,_,_,_]:={0,0}
MyProjection[r_,b_,c_,tower_?MatrixQ]:=Module[{t,k,B,i,a,ct,L,w,u,v},
t=tower[[-1]][[1]];
k=Exponent[r,t];
Sow[Timing[
Basis[k,tower];
][[1]],"Basis"];
MyAssert[KeyExistsQ[TowerInfo,t]];
B=TowerInfo[t][[5]];

{u,v}={Table[0,{k+2}],CoefficientList[r,t]};
Do[
	a=v[[+1+k-i]];
	(*a=Coefficient[v,t,k-i];*)\.b4
	ct=Rational`MyCoefficientNew[tower[[;;,1]],a,b];
	
	If[ct=!=0,L=B[[k-i+1]];
	w=Cancel[ct/c];
	u[[;;Length[L[[1]]]]]+=w L[[1]];
	v[[;;Length[L[[2]]]]]-=w L[[2]];
	(*{u,v}={Collect[u+w*L[[1]],t,MyTogether],Collect[v-w*L[[2]],t,MyTogether]};*)
	
	];
,{i,0,k}];
Return[{Sum[MyTogether[u[[+1+i]]]t^i,{i,0,k+1}],Sum[MyTogether[v[[+1+i]]]t^i,{i,0,k}]}];
];


(* ::Text:: *)
(*Input : A tower as required by function CRforSimpleDR, where the last extension is a Sigma extension t*)
(*          a polynomial p in t*)
(*    Output : {q, r}, r in the auxiliary space such that*)
(*               p = \[CapitalDelta] (q) + r*)


(*not used*)
Clear[AuxiliaryReduction]
AuxiliaryReduction[p_,tower_?MatrixQ]:=Module[{t,d,pCoeffs,beta,pt,q,r,lc,g,u,tower1},
If[p===0,Return[{0,0}]];
{t,beta}=tower[[-1,{1,3}]];
pt =p; {q,r}={0,0};
tower1=Drop[tower,-1];


pCoeffs=(MyTogether/@CoefficientList[p,t]);
Do[
	If[pCoeffs[[+1+d]]===0,Continue[]];
	{g,u}=CRforSimpleDR[pCoeffs[[+1+d]],tower1];
	{q,r}+= {g,u}*t^d;
	pCoeffs[[;;d]]-=MySigma[g,tower1] Table[Binomial[d,i] beta^(d-i),{i,0,d-1}];
,{d,Length[pCoeffs]-1,0,-1}];
(*r=Sum[pCoeffs[[i]]t^(i-1),{i,Length[pCoeffs]}];*)
Return[{q,r}];
];


(* ::Subsection::Closed:: *)
(*RPi-Case*)


MyGetOrderOfUnity::donotrecognizeroot="Error: Failed to find order of `1`. Are you sure this is a root of unity in Complex? (of order <1000)";
Clear[MyGetOrderOfUnity];
MyGetOrderOfUnity[alpha_]:=Module[{i=1,alphaj=1}
,While[!PossibleZeroQ[1-(alphaj*=alpha),Method->"ExactAlgebraics"]&&i<1000,
i++;
];
If[i==1000,Message[MyGetOrderOfUnity::donotrecognizeroot,alpha];Abort[];,Return[i]];
]


(* ::Text:: *)
(*Input: A tower as required by function CRforSimpleDR, where the last extension is an R-extension {y,alpha,0}*)
(*        g, an element in the tower (not necessarily simplified or canonocalized)*)
(*  Output: {gS,gR}, two elements in the tower s.t.*)
(*             g=\[CapitalDelta](gS)+gR*)
(*          is a complete reduction of g. gR is simplified (in particular gR === 0 if gR can be simplified to zero)*)


(*Clear[BasicRReduction]
BasicRReduction[g_,f_,tower_?MatrixQ]:=Module[{y=tower[[-1,1]],AAA},
PiReduction[Collect[g,y]/.y^(AAA_)->y^Mod[AAA,TowerInfo["R-Extension"][[1,3]]],f,tower]]*)


(* ::Text:: *)
(*Input: A tower as required by function CRforSimpleDR, where the last extension is a Pi-extension {p,a,0}*)
(*        g, an element in the tower (not necessarily simplified or canonicalized)*)
(*        s, an invertible element in the tower.*)
(*  Output: {gS,gR}, two elements in the tower s.t.*)
(*             g=\[CapitalDelta]_s(gS)+gR*)
(*          is a complete reduction of g. gR is simplified (in particular gR === 0 if gR can be simplified to zero)*)
(*   Note: If m != 0, the complementary space is currently F[t]_{< |m|}, the space of polynomials of degree less than the absolute value of m, where m is the degree of p;. *)


Clear[PiReduction];
PiReduction[0,_,tower_?MatrixQ]:={0,0}
PiReduction[g_,s_,towerIn_?MatrixQ]:=Module[
{st,sc,i,degG,gS,gR,gcS,gcR,tdegG,gCoeffs,t,h,a,m,tower=Most[towerIn],lo,up},
MyAssert[towerIn[[-1,3]]===0];
{t,a}=towerIn[[-1,1;;2]];
(*g=Collect[gIn,t,MyTogether];*)
m=Exponent[s,t];
MyAssert[m==-Exponent[s,t^-1]];
tdegG=-Exponent[g,t^(-1)];
(*degG=Exponent[g,t];*)
(*If[tdegG>degG,Return[{0,0}]];*)
If[tdegG===\[Infinity],Return[{0,0}]];
gCoeffs=CoefficientList[g t^(-tdegG),t];
If[Length[gCoeffs]==0,Return[{0,0}]];
degG=Length[gCoeffs]+tdegG-1;
If[m==0,
	{gS,gR}=Sum[
	CRforSimpleDR[gCoeffs[[i-tdegG+1]],s a^i,tower]t^i
	,{i,tdegG,degG}];
	MyAssert[MyTogether[DeltaF[gS,s,towerIn]+gR-g]===0];
	Return[{gS,gR}];
];
sc=(s/.t->1);
(*Print["g= ",g];*)
{lo,up}=If[m>0,{0,m-1},{m,-1}];
If[degG<up,gCoeffs=Join[gCoeffs,Table[0,up-degG]]];
If[tdegG>lo,gCoeffs=Join[Table[0,tdegG-lo],gCoeffs]];
(*gCoeffs=If[m>0,
	PadRight[gCoeffs,Max[degG,Abs[m]-1]-Min[tdegG,0]+1,0,Max[tdegG,0]]
,
	PadRight[gCoeffs,Max[degG,-1]-Min[tdegG-m,0]+1,0,Max[tdegG-m,0]]
];*)
(*Print["gCoeffs= ",gCoeffs];*)
st=Min[tdegG,lo]-1; (*exponent of first entry in gCoeffs*)
gS=0;
If[m>0,
	Do[
		gCoeffs[[i+m-st]]+=sc a^i MySigma[gCoeffs[[i-st]],tower];
		gS-=gCoeffs[[i-st]]t^i;	
	,{i,tdegG,lo-1}];
	Do[
		h=MySigma[gCoeffs[[i-st]]/(sc a^(i-m)),-1,tower];
		gCoeffs[[i-m-st]]+=h;
		gS+=h t^(i-m);	
	,{i,degG,up+1,-1}];
	
];
If[m<0,
	Do[
		h=MySigma[gCoeffs[[i-st]]/(sc a^(i-m)),-1,tower];
		gCoeffs[[i-m-st]]+=h;
		gS+=h t^(i-m);	
	,{i,tdegG,lo-1}];
	Do[
		gCoeffs[[i+m-st]]+=sc a^i MySigma[gCoeffs[[i-st]],tower];
		gS-=gCoeffs[[i-st]]t^i;	
	,{i,degG,up+1,-1}];
];
gR=Sum[MyTogether[gCoeffs[[i-st]]] t^i,{i,lo,up}];
(*Print[{m,gR//Factor}];*)
MyAssert[MyTogether[DeltaF[gS,s,towerIn]+gR-g]===0];
Return[{gS,gR}];
];


Clear[SimpleRReduction]
SimpleRReduction[g_,f_,tower_?MatrixQ]:=Module[{t=tower[[-1,1]],a=tower[[-1,2]],s,mu,m,d,lambda,AAA,p,gCoeffs,gProj,i,j,gS,iPrime,k,u,v,towerMu,gR},
MyAssert[tower[[-1,3]]===0];
lambda=(t/.(Rule@@@(TowerInfo["R-Extension"][[;;,{1,3}]])));MyAssert[IntegerQ[lambda]];
m=Exponent[f,t];
s=Coefficient[f,t,m];
MyAssert[MyTogether[f-s t^m]===0];
If[m==0,Return[PiReduction[Collect[g,t]/.t^AAA_->t^Mod[AAA,lambda],f,tower]]];
d=GCD[lambda,m];
(*Print["d=  ",d];*)
mu=lambda/d;
p[i_,k_]:=p[i,k]=MyTogether[Product[MySigma[s a^i,l,tower],{l,0,k-1}]Product[Product[MySigma[ a^m,l,tower],{l,0,ll-1}],{ll,1,k-1}]];
gCoeffs=CoefficientList[g,t];
If[gCoeffs==={},Return[{0,0}]];
gCoeffs=MyTogether[Total[Partition[gCoeffs,lambda,lambda,1,0]]];
MyAssert[Length[gCoeffs]<=lambda];
gProj=PadRight[gCoeffs[[;;UpTo[d]]],d];
gS=0;
Do[
	u=gCoeffs[[+1+i]];
	iPrime=Mod[i,d];
	k=MyExtendedGCD[m,lambda,iPrime-i][[1]];
	gS+=-Sum[MySigma[u,j,tower]p[i,j]t^Mod[i+j m,lambda],{j,0,k-1}];
	gProj[[+1+iPrime]]+=MySigma[u,k,tower]p[i,k];
,{i,d,Length[gCoeffs]-1}];
MyAssert[MyTogether[DeltaF[gS,f,tower]+Sum[gProj[[+1+i]]t^i,{i,0,d-1}]-g]===0];

towerMu=MyChangeShiftTower[tower[[;;-2]],mu];
Do[
	v=gProj[[+1+i]];
	{u,gProj[[+1+i]]}=CRforSimpleDR[v,p[i,mu],towerMu];
	gS+=Sum[MySigma[u,j,tower]p[i,j]t^Mod[i+j m,lambda],{j,0,mu-1}];
,{i,0,d-1}];
gR=Sum[gProj[[+1+i]]t^i,{i,0,d-1}];
(*Print[{gS,f,tower,gR,g}];*)
MyAssert[MyTogether[DeltaF[gS,f,tower]+gR-g]===0];
Return[{gS,gR}];
];



Clear[MyExtendedGCD];
MyExtendedGCD[a_,b_,c_]:=Module[{g,ag,bg,aC,bC,k},
MyAssert[Divisible[c, GCD[a,b]]];
{g,{ag,bg}}=ExtendedGCD[a,b];
{aC,bC}={ag,bg}*c/g;
{k,aC}=QuotientRemainder[aC,b];
bC+=a k;
MyAssert[aC a+bC b===c];
MyAssert[0<=aC<b];
Return[{aC,bC}]
]


(* ::Subsection::Closed:: *)
(*Idempotent*)


Clear[Project];
Project[f_,a_List,k_List,y_List]:=With[{alphas=Table[((-1)^(2/a[[i]]))^(a[[i]]-1-k[[i]]),{i,1,Length[y]}]},
	MyTogether[f/.Thread[Rule[y,alphas]]]]//ToRadicals


Clear[e];
e[l_List,k_List,y_List,alphas_]:=Times@@MapThread[e,{l,k,y,alphas}]
e[l_List,k_List,y_List]:=Times@@MapThread[e,{l,k,y}]
e[l_,kIn_,y_]:=e[l,kIn,y,(-1)^(2/l)]
e[l_,kIn_,y_,alpha_]:=e[l,Mod[kIn,l],y]=Module[{j,k=Mod[kIn,l]},(Times@@Drop[Table[y-(alpha)^j,{j,0,l-1}],{l-1-k+1}])
/(Times@@Drop[Table[(alpha)^(l-1-k)-(alpha)^j,{j,0,l-1}],{l-1-k+1}])//RootReduce//ToRadicals];


Clear[RemoveRMonomials];
RemoveRMonomials::NotAnRExtension="Error: Tower `1` extends the constants";
RemoveRMonomials::malformedTower="Error: Tower `1` is malformed or does not fit to list of R-monomials to remove";
RemoveRMonomials[tower_?MatrixQ,yList_List,proj_Integer:-1]:=Module[{curOrd,ordList,alphasProj,newtower,alpha},
ordList={};
newtower=tower;
Do[
	If[!MemberQ[yList,tower[[i,1]]],Continue[]];
	curOrd=MyGetOrderOfUnity[newtower[[i,2]]];
	If[curOrd==1,Message[RemoveRMonomials::NotAnRExtension,tower];Abort[]];
	alpha=newtower[[i,2]];
	 newtower=MyChangeShiftTower[newtower,curOrd];
	newtower[[;;,2;;]]=(newtower[[;;,2;;]]/.tower[[i,1]]->alpha^Mod[curOrd-1-proj,curOrd]);
	AppendTo[ordList,curOrd];
,{i,Length[tower]}];
newtower[[;;,2;;]]=MyTogether[newtower[[;;,2;;]]];
 newtower=Select[newtower,(Rest[#]=!={1,0})&];
If[Length[newtower]+Length[yList]!=Length[tower],
Message[RemoveRMonomials::malformedTower,tower];Abort[]];
Return[{newtower,ordList}];
]


Clear[IdempotentReduction];
Options[IdempotentReduction]={"SimplifyFullOutput"->False}
IdempotentReduction::NotPlainDelta="f = `1` must be 1 for a non-simple tower. Only plain \[CapitalDelta] is supported for a non-simple tower";
IdempotentReduction::NotRExtension="No R-monomial in tower `1`";
IdempotentReduction[g_,f_,tower_?MatrixQ,OptionsPattern[]]:=Module[{ordList,fm,numR,orders,gm,yList,newtower,ord,gS,gR,gSn,gRn,alphas,k,myE},
If[!KeyExistsQ[TowerInfo["R-Extension"]],Message[IdempotentReduction::NotRExtension,tower];Abort[];];
If[f=!=1,Message[IdempotentReduction::NotPlainDelta,f];Abort[]];
Sow[Timing[
numR=Length[TowerInfo["R-Extension"][[;;,1]] \[Intersection] tower[[;;,1]]];
{yList,alphas,orders}=Transpose[TowerInfo["R-Extension"][[;;numR]]];
myE=e[orders,orders*0,yList,alphas];
{newtower,ordList}=RemoveRMonomials[tower,yList,0];
ord=Times@@ordList;
(*gS=-Sum[Sum[MySigma[myE,j,tower],{j,k+1,ord-1}]MySigma[g,k,tower],{k,0,ord-1}]/.Thread[yList^(AAA121212_)->yList^Mod[AAA121212,orders]];*)
gS=Sum[Sum[MySigma[myE,i-j,tower]MySigma[g,-j,tower],{j,1,i}],{i,1,ord-1}]/.Thread[yList^(AAA121212_)->yList^Mod[AAA121212,orders]];
(*Print[{gS,e[orders,orders-1,yList]Sum[MySigma[g,k,tower],{k,0,ord-1}]}];*)
(*Print["gS= ",Together[gS]];*)
gm=Sum[MySigma[g,-k,tower]/.Thread[yList->1/alphas],{k,0,ord-1}];
(*Print["gm = ",MyTogether[gm]];*)
MyAssert[CheckReduction[{g,f},{gS,myE gm},tower]];
fm=1;
{gSn,gRn}=CRforSimpleDR[gm,fm,newtower];
(*Print["{gSn,gRn}= ",{gSn,gRn}];*)
gR=myE gRn;
gS+=Sum[MySigma[myE gSn,k,tower],{k,0,ord-1}];
][[1]],"IdempotentReduction"];
MyAssert[CheckReduction[{g,f},{gS,gR},tower]];
Return[{If[OptionValue["SimplifyFullOutput"],MyTogether[gS],gS],gR}];
]


(* ::Subsection:: *)
(*Creative/Parametric Telescoping *)


Clear[FindSummableCombination]
FindSummableCombination[SigmaPairList_?MatrixQ,nonConsts_List]:=Module[{commonDen,R,c,m,B,i,j,Sol,n,sol},
R=SigmaPairList[[;;,2]];
n=Length[SigmaPairList];
If[MatchQ[R,{0..}],Return[Table[{sol,sol . SigmaPairList[[;;,1]]},{sol,IdentityMatrix[n]}]]];
commonDen=PolynomialLCM@@Denominator/@R;
B=Flatten/@PadRight[CoefficientList[Table[Numerator[R[[i]]]Cancel[commonDen/Denominator[R[[i]]]],{i,n}],nonConsts]];
Sol=If[MatrixRankHeuristic[B]<n,NullSpace[Transpose[B]],{}];
If[Sol==={},Return[{}]];
Return[Table[{sol,sol . SigmaPairList[[;;,1]]},{sol,Sol}]]
]


Clear[ParametricTelescopingViaCR];
ParametricTelescopingViaCR[tower_List,F_List]:= Module[{n,A,R,c,clist,coeff,m,B,i,j,Sol},
n=Length[F];
ResetTower[tower];
A=CRforSimpleDR[#,tower]&/@F;
A=MapAt[MyTogether,A,{All,2}];
Return[FindSummableCombination[A,tower[[;;,1]]]];
]



Clear[CreativeTelescopingViaCR]
CreativeTelescopingViaCR::norecfound="No recurrence of order <= `1` exists, increase value of option \"MaxOrder\"";

Options[CreativeTelescopingViaCR]={"MaxOrder"->30,"WithNegativeShifts"->False,"SimplifyFullOutput"->False};
CreativeTelescopingViaCR[g_,{towerN_List,towerK_List},opts:OptionsPattern[]]:=CreativeTelescopingViaCR[g,{towerN,towerK},OptionValue["WithNegativeShifts"],opts]
CreativeTelescopingViaCR[g_,{towerN_List,towerK_List},False,OptionsPattern[]]:=Module[{comb,gPairList,m,gmS,gmR},
gPairList={};
ResetTower[towerK];
{gmS,gmR}={0,0};
Do[
	{gmS,gmR}=CRforSimpleDR[If[m==0,g,MySigma[gmR,towerN]],towerK]+{MySigma[gmS,towerN],0};
	gmR=MyTogether[gmR];(* for FindSummableCombination it should be together*)
	MyAssert[MyTogether[DeltaF[gmS,1,towerK]+gmR-MySigma[g,m,towerN]]===0];
	AppendTo[gPairList,{gmS,gmR}];
	Sow[Timing[
	comb=FindSummableCombination[gPairList,towerK[[;;,1]]];
	][[1]],"FindSummableCombination"];
	If[comb=!={},MyAssert[MyTogether[Sum[comb[[1,1,i]]MySigma[g,i-1,towerN],{i,Length[comb[[1,1]]]}]-DeltaF[comb[[1,-1]],1,towerK]]===0];Break[]];
	(*Print["m:",m," New Remainder: ",gmR];*)
,{m,0,OptionValue["MaxOrder"]}];
If[comb==={},Message[CreativeTelescopingViaCR::norecfound,OptionValue["MaxOrder"]]];
Return[If[OptionValue["SimplifyFullOutput"],MyTogether[comb[[1]]],comb[[1]]]];
]

CreativeTelescopingViaCR[g_,{towerN_List,towerK_List},True,OptionsPattern[]]:=Module[{result,comb,gPairList,m,gmS,gmR,shift,sign,lastP},
gPairList={};
ResetTower[towerK];
{gmS,gmR}={0,0};
lastP={0,g};
Do[
	sign=If[EvenQ[m],-1,1];
	shift=sign Ceiling[m/2];
	{gmS,gmR}=CRforSimpleDR[If[m==0,g,MySigma[lastP[[2]],sign,towerN]],towerK]+{MySigma[lastP[[1]],sign,towerN],0};
	gmR=MyTogether[gmR];(* for FindSummableCombination it should be together*)
	MyAssert[MyTogether[DeltaF[gmS,1,towerK]+gmR-MySigma[g,shift,towerN]]===0];
	If[sign>0,AppendTo[gPairList,{gmS,gmR}],PrependTo[gPairList,{gmS,gmR}]];
	Sow[Timing[
	comb=FindSummableCombination[gPairList,towerK[[;;,1]]];
	][[1]],"FindSummableCombination"];
	If[comb=!={},
		result=MySigma[comb[[1]],Floor[m/2],towerN];
		result[[1]]=MyTogether[result[[1]]];
		MyAssert[MyTogether[Sum[result[[1,i]]MySigma[g,i-1,towerN],{i,Length[result[[1]]]}]-DeltaF[result[[-1]],1,towerK]]===0];
		Break[]
	];
	lastP=gPairList[[sign]];
	(*Print["m:",m," New Remainder: ",gmR];*)
,{m,0,OptionValue["MaxOrder"]}];
If[comb==={},Message[CreativeTelescopingViaCR::norecfound,OptionValue["MaxOrder"]]];
Return[If[OptionValue["SimplifyFullOutput"],MyTogether[result],result]];
]


(* ::Subsection::Closed:: *)
(*Deprecated (not used)*)


(*deprecated*)
Clear[AuxiliaryReductionO]
AuxiliaryReductionO[p_,tower_List]:=Module[{t,pt,q,r,d,lc,g,u,tower1},
If[p===0,Return[{0,0}]];
t=tower[[-1]][[1]];
pt =Collect[p,t,MyTogether]; {q,r}={0,0};
tower1=Drop[tower,-1];
While[pt=!=0,
d =Exponent[pt,t];
lc=Coefficient[pt,t,d];
{g,u}=CRforSimpleDR[lc,tower1];
q+= g*t^d;
r+= u*t^d;
pt=Collect[pt-MySigma[g*t^d,1,tower]+g*t^d-u*t^d,t,MyTogether];
MyAssert[Exponent[pt,t]<d];
];
{q,r}
];


(* ::Input::Initialization:: *)
(* Input:a \Sigma tower represented by{{x,1,1},{t_1,1,b_1},{t_2,1,b_2},...{t_n,1,b_n}} and
        a nonnegative integer k
    Output: {{u_0,v_0},...,{u_k,v_k}} such that v_0,...,v_k form a C-basis of the intersection of \[CapitalDelta](F_{n-1}(t_n))and the auxiliary space  
Remark:n>1            
*)


(*deprecated*)
Clear[Basis];
Basis[k_Integer,tower_List]:=Module[{n=Length[tower],t=tower[[-1,1]],H,lt,v0,m,L,i,a,b,q,r,u,v},
MyAssert[KeyExistsQ[TowerInfo,t]];
H=TowerInfo[t];
lt=H[[1]];
v0=H[[2]];
L=H[[5]];
m=Length[L];
Do[
	a=t^(i+1)/(i+1)-lt*t^i;
	b=MySigma[a,1,tower]-a-v0*t^i;
	{q,r}=AuxiliaryReduction[b,tower];
	u = a-q;
	v=r+v0*t^i;
	AppendTo[L,MyTogether[CoefficientList[{u,v},t]]]
,{i,m,k}];
TowerInfo[t]={H[[1]],H[[2]],H[[3]],H[[4]],L};
]





(* deprecated *)
$activateEcho=False;
Clear[CollectTowerInfo];
oCollectTowerInfo[tower_List]:=Module[{n,i,g,r,b,c,B,G},
n=Length[tower];
TowerInfo={};
For[i=2,i<=n,i++,
	G=tower[[;;i-1]];
	{g,r}=CRforSimpleDR[tower[[i,3]],G];
	{b,c}=Rational`BasisElement[tower[[1;;i-1,1]],r];
	B={{tower[[i,1]]-g,r}};
	AppendTo[TowerInfo,{g,r,b,c,B}];
];
TowerInfo=AssociationThread[tower[[2;;,1]]->TowerInfo]
]


(* ::Subsection:: *)
(*End of package*)


(* ::Input::Initialization:: *)
End[];


(* ::Input::Initialization:: *)
EndPackage[];
