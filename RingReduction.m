(* ::Package:: *)

(* ::Input::Initialization:: *)
BeginPackage["RingReduction`"];
ClearAll@@Names["RingReduction`*"];


(* ::Input::Initialization:: *)
GetCoprimeFactorization::usage="";
LocalNormalReduction::usage="";
NormalReduction::usage="";
AuxiliaryReduction::usage="";
MyProjection::usage="";
SigmaRingReduction::usage="";
RingReduction::usage="TowerInfo must be initialized before using this function 
(with ReInitTower[tower];)
Call: RingReduction[g,f,tower]
where:
	tower: A basic RPiSigma tower represented by
	{{x,1,1},{p_1,a_1,0},...{p_m,a_m,0},{y,alpha,0},{t_1,1,b_1},{t_2,1,b_2},...{t_n,1,b_n}}
	(m>=0,n>=0 and with or without the R-monomial y)
	g: An element in this ring
	f: An invertible element in this ring. f must be f=1 if n>0 or if y is in the tower.
       Can be left out, in this case f=1
Out: {gS,gR}, with \[CapitalDelta]_f(gS)+gR===g, where gR is a remainder";
IdempotentReduction::usage=""
ReInitTower::usage="(Re)Initializes TowerInfo. Call at the beginning and whenever a new tower is used";
PT ::usage="";
MyTogether::usage="";
DeltaF::usage="";
MyTSigma::usage="";
CheckReduction::usage="";
MyGetOrderOfUnity::usage="";
RemoveRMonomials::usage="";
FindTeleskopingRecurrence::usage="";


$UseIdempotentReduction=True;


usenewversionForRepresentatives=True;


(* ::Input::Initialization:: *)
Begin["`Private`"];


(* ::Subsection::Closed:: *)
(*Main*)


(* ::Text:: *)
(*Main scheduler which calls Reduction-function which fits to this tower. *)
(**)
(*In : a basic RPiSigma tower represented by*)
(*	{{x, 1, 1}, {p_ 1, a_ 1, 0}, ... {p_m, a_m, 0}, {y, alpha, 0}, {t_ 1, 1, b_ 1}, {t_ 2, 1, b_ 2}, ... {t_n, 1, b_n}}*)
(*	(m >= 0, n >= 0 and with or without R - monomial y)*)
(*	g : An element in this ring*)
(*	f : An invertible element in this ring . Must be f = 1 if n > 0*)
(*	TowerInfo must be initialized before using this function *)
(*	(with ReInitTower[tower]; or with information which was produced for this tower)*)
(**)
(*Out : {gS, gR}, with \[CapitalDelta]_f (gS) + gR === g, where gR is a remainder*)
(**)


(*Note: The Sow[Timing[ ][[1]],String] is used for benchmarking*)
Clear[RingReduction];
RingReduction::malformedTower="Error: Tower `1` is malformed and not fit for RingReduction w.r.t Delta `2`";
RingReduction[0,_,_?MatrixQ,OptionsPattern[]]:={0,0}
RingReduction[g_,tower_?MatrixQ,opts:OptionsPattern[]]:=RingReduction[g,1,tower,opts];
RingReduction[g_,f_,tower_?MatrixQ,OptionsPattern[]]:=Module[{gTrans,fTrans,step,found,x,alpha,beta,gS,gR},
Assert[Head[TowerInfo]===Association];
Sow[Timing[
If[Length[tower]==1&&tower[[1,2]]===1,
	{x,step}=tower[[1,{1,3}]];
	If[step=!=1,
		gTrans=(g/.x->step x);
		fTrans=MyTogether[(f/.x->step x)];
	,
		{fTrans,gTrans}={f,g};
	];
	If[!usenewversionForRepresentatives,
		If[!KeyExistsQ[TowerInfo,x],TowerInfo[x]={}];
		{{gS,gR},TowerInfo[x]}=RationalReduction`RationalReduction[gTrans,fTrans,{{x,1,1}},"Representatives"->TowerInfo[x]];	
		
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
	Message[RingReduction::malformedTower,tower,f];
	Abort[];
];]];
][[1]],ToString[tower[[-1,1]]]<>" combined"];
Assert[CheckReduction[{g,f},{gS,gR},tower]];
Return[{gS,gR}];
]


(* ::Text:: *)
(*Input :  An admissible tower (as specified for function RingReduction). *)
(*    Output : Null*)
(*    Side effect : If there is no R-extension then*)
(*         TowerInfo=<| |>,*)
(*           otherwise if there is an R - extension {y, alpha, 0} in the tower*)
(*        TowerInfo = <|"R-Extension" -> {y, lambda}|>,  where lambda = ord (alpha)*)


ReInitTower::malformedTower="Error: Tower `1` contains more than one R-extension, this is not implemented";
Clear[ReInitTower]
ReInitTower[tower_?MatrixQ]:=Module[{newtower,ordList,alphas,yList,RExt},
TowerInfo=<||>;
(*If[Length[RExt]>1,Message[ReInitTower::malformedTower,tower];Abort[]];*)
newtower=tower;
While[True,
	RExt=Select[newtower,(#[[3]]===0 && RootOfUnityQ[#[[2]]])&];
	If[Length[RExt]==0,Break[]];
	yList=RExt[[;;,1]];
	alphas=(MyGetOrderOfUnity/@RExt[[;;,2]]);
	Assert[Union[MyTogether[Select[tower,MemberQ[yList,#[[1]]]& ][[;;,2]]^alphas]][[1]]===1];
	If[!KeyExistsQ[TowerInfo,"R-Extension"],TowerInfo["R-Extension"]={}];
	TowerInfo["R-Extension"]=
		SortBy[Join[TowerInfo["R-Extension"],Transpose[{yList,alphas}]],FirstPosition[tower[[;;,1]],#[[1]]][[1]]&];
	{newtower,ordList}=RemoveRMonomials[newtower,yList];
	Assert[ordList===alphas];
	Assert[Length[newtower]+Length[TowerInfo["R-Extension"]]==Length[tower]];
]

];


(* ::Subsection::Closed:: *)
(*Auxiliary Functions*)


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
(*Chooses the best way to simplify the given object. The output is canonical w.r.t. the R-extension.*)
(*Nothing for QQ,*)
(*plain MyTogether for QQ (x_ 1, x_ 2, ...),*)
(*MyEliminateRootObjects for algebraic numbers *)
(* (Mathematica is really bad at dealing with algebraic numbers like (-1)^(2/3))*)


Clear[MyTogether]
Attributes[MyTogether]={Listable}
MyTogether[f_]:=
If[Length[Variables[f]]==0,
MyEliminateRootObjects[f]
,If[KeyExistsQ[TowerInfo,"R-Extension"],
   With[{yL=TowerInfo["R-Extension"][[;;,1]],l=TowerInfo["R-Extension"][[;;,2]]},
	If[(Intersection[Variables[f],yL]=!={})(*&&Exponent[f,y]>=l*),
	Together[MyEliminateRootObjects[(Collect[f,yL]/.Thread[yL^(AAA121212_)->yL^Mod[AAA121212,l]])],Extension->Automatic]
,
	Together[MyEliminateRootObjects[f],Extension->Automatic]
	]]
,
	Together[MyEliminateRootObjects[f],Extension->Automatic]
]
]



(* ::Subsection:: *)
(*Re-used*)


$activateEcho=False;
Clear[myEcho];
myEcho[args___]:=If[$activateEcho,Echo[args]];


Clear[MyTSigma]
MyTSigma[expr_,0,___]:=expr
MyTSigma[expr_,rest__]:=If[Variables[expr]==={},expr,Sigma`DifferenceFields`BasicTools`DFInterface`TSigma[expr,rest,False]]/.Sigma`Algebra`CompAlgSigma`II->I;


Clear[DeltaF];
DeltaF[g_,f_,tower_?MatrixQ]:=f MyTSigma[g,1,tower]-g


Clear[MyEliminateRootObjects];
Attributes[MyEliminateRootObjects]={Listable}
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
Assert[CheckReduction[{beta,1},{betaS,betaR},tower]];

pCoeffs=CoefficientList[p,t];
Do[
	If[pCoeffs[[+1+d]]===0,Continue[]];
	{g,u}=RingReduction[pCoeffs[[+1+d]],tower1];
	If[g===0 && u===0,Continue[]];
	ct=Rational`MyCoefficientNew[tower[[;;,1]],u,b];
	w=MyTogether[ct/c];
	{q,r}+= {w/(d+1) t^(d+1)+(g-w betaS)*t^d,MyTogether[u-w*betaR]t^d};
	
	Assert[Rational`MyCoefficientNew[tower[[;;,1]],u-w*betaR,b]===0];
	sub=If[Length[tower]>1,Collect[MyTSigma[g-w betaS,tower1],tower[[-2,1]],MyTogether],MyTogether[MyTSigma[g-w betaS,tower1]]];
	pCoeffs[[;;d]]-=sub Table[Binomial[d,i] beta^(d-i),{i,0,d-1}];
	pCoeffs[[;;d]]-=Table[w/(d+1) Binomial[d+1,i] beta^(d+1-i),{i,0,d-1}];
	
,{d,Length[pCoeffs]-1,0,-1}];
(*r=Sum[pCoeffs[[i]]t^(i-1),{i,Length[pCoeffs]}];*)
Return[{q,r}];
];


(* ::Text:: *)
(*Input: A tower as required by function RingReduction, where the last extension is a Sigma extension {t,1,beta}*)
(*        g, an element in the tower (not necessarily simplified or canonocalized)*)
(*  Output: {gS,gR}, two elements in the tower s.t.*)
(*             g=\[CapitalDelta](gS)+gR*)
(*          is a complete reduction of g. gR is simplified (in particular gR === 0 if gR can be simplified to zero)*)


SigmaRingReduction[0,_]:={0,0}
SigmaRingReduction[g_,tower_?MatrixQ]:=Module[{t=tower[[-1,1]],pp=g,q,r,b,c,u=0,v},
Assert[tower[[-1,2]]===1];

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


Clear[TowerPrecomp];
TowerPrecomp[tower_?MatrixQ]:=Module[{t,beta,g,r,b,c,B},
{t,beta}=tower[[-1,{1,3}]];
Assert[!KeyExistsQ[TowerInfo,t]];
{g,r}=RingReduction[beta,tower[[;;-2]]];
{b,c}=Rational`BasisElement[tower[[1;;-2,1]],r];
B={{{-g,1},{r}}};
TowerInfo[t]={MyTogether[g],r,b,c,B};
]


Clear[CheckReduction]
CheckReduction[{g_,f_},{gS_,gR_},tower_]:=(MyTogether[DeltaF[gS,f,tower]+gR-g]===0)


(* ::Text:: *)
(*Input :  A tower as required by function RingReduction, where the last extension is a Sigma extension t*)
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
Assert[KeyExistsQ[TowerInfo,t]];
B=TowerInfo[t][[5]];

{u,v}={Table[0,{k+2}],CoefficientList[r,t]};
Do[
	a=v[[+1+k-i]];
	(*a=Coefficient[v,t,k-i];*)
	
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
(*Input : A tower as required by function RingReduction, where the last extension is a Sigma extension t*)
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
	{g,u}=RingReduction[pCoeffs[[+1+d]],tower1];
	{q,r}+= {g,u}*t^d;
	pCoeffs[[;;d]]-=MyTSigma[g,tower1] Table[Binomial[d,i] beta^(d-i),{i,0,d-1}];
,{d,Length[pCoeffs]-1,0,-1}];
(*r=Sum[pCoeffs[[i]]t^(i-1),{i,Length[pCoeffs]}];*)
Return[{q,r}];
];


(* ::Subsection::Closed:: *)
(*RPi-Case*)


MyGetOrderOfUnity::donotrecognizerot="Error: Failed to find order of `1`. Are you sure this is a root of unity in Complex? (of order <1000)";
Clear[MyGetOrderOfUnity];
MyGetOrderOfUnity[alpha_]:=Module[{i=1,alphaj=1}
,While[!PossibleZeroQ[1-(alphaj*=alpha),Method->"ExactAlgebraics"]&&i<1000,
i++;
];
If[i==1000,Message[MyGetOrderOfUnity::donotrecognizerot,alpha];Abort[];,Return[i]];
]


(* ::Text:: *)
(*Input: A tower as required by function RingReduction, where the last extension is an R-extension {y,alpha,0}*)
(*        g, an element in the tower (not necessarily simplified or canonocalized)*)
(*  Output: {gS,gR}, two elements in the tower s.t.*)
(*             g=\[CapitalDelta](gS)+gR*)
(*          is a complete reduction of g. gR is simplified (in particular gR === 0 if gR can be simplified to zero)*)


Clear[BasicRReduction]
BasicRReduction[g_,1,tower_?MatrixQ]:=Module[{y=tower[[-1,1]],AAA},
PiReduction[Collect[g,y]/.y^(AAA_)->y^Mod[AAA,TowerInfo["R-Extension"][[1,2]]],1,tower]]


(* ::Text:: *)
(*Input: A tower as required by function RingReduction, where the last extension is a Pi-extension {p,a,0}*)
(*        g, an element in the tower (not necessarily simplified or canonocalized)*)
(*        s, an invertible element in the tower.*)
(*  Output: {gS,gR}, two elements in the tower s.t.*)
(*             g=\[CapitalDelta]_s(gS)+gR*)
(*          is a complete reduction of g. gR is simplified (in particular gR === 0 if gR can be simplified to zero)*)
(*   Note: If m != 0, the complementary space is currently F[t]_{< |m|}, the space of polynomials of degree less than the absolute value of m, where m is the degree of p;. *)


Clear[PiReduction];
PiReduction[0,_,tower_?MatrixQ]:={0,0}
PiReduction[g_,s_,towerIn_?MatrixQ]:=Module[
{st,sc,i,degG,gS,gR,gcS,gcR,tdegG,gCoeffs,t,h,a,m,tower=Most[towerIn],lo,up},
Assert[towerIn[[-1,3]]===0];
{t,a}=towerIn[[-1,1;;2]];
(*g=Collect[gIn,t,MyTogether];*)
m=Exponent[s,t];
Assert[m==-Exponent[s,t^-1]];
tdegG=-Exponent[g,t^(-1)];
(*degG=Exponent[g,t];*)
(*If[tdegG>degG,Return[{0,0}]];*)
If[tdegG===\[Infinity],Return[{0,0}]];
gCoeffs=CoefficientList[g t^(-tdegG),t];
If[Length[gCoeffs]==0,Return[{0,0}]];
degG=Length[gCoeffs]+tdegG-1;
If[m==0,
	{gS,gR}=Sum[
	RingReduction[gCoeffs[[i-tdegG+1]],s a^i,tower]t^i
	,{i,tdegG,degG}];
	Assert[MyTogether[DeltaF[gS,s,towerIn]+gR-g]===0];
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
		gCoeffs[[i+m-st]]+=sc a^i MyTSigma[gCoeffs[[i-st]],tower];
		gS-=gCoeffs[[i-st]]t^i;	
	,{i,tdegG,lo-1}];
	Do[
		h=MyTSigma[gCoeffs[[i-st]]/(sc a^(i-m)),-1,tower];
		gCoeffs[[i-m-st]]+=h;
		gS+=h t^(i-m);	
	,{i,degG,up+1,-1}];
	
];
If[m<0,
	Do[
		h=MyTSigma[gCoeffs[[i-st]]/(sc a^(i-m)),-1,tower];
		gCoeffs[[i-m-st]]+=h;
		gS+=h t^(i-m);	
	,{i,tdegG,lo-1}];
	Do[
		gCoeffs[[i+m-st]]+=sc a^i MyTSigma[gCoeffs[[i-st]],tower];
		gS-=gCoeffs[[i-st]]t^i;	
	,{i,degG,up+1,-1}];
];
gR=Sum[MyTogether[gCoeffs[[i-st]]] t^i,{i,lo,up}];
(*Print[{m,gR//Factor}];*)
Assert[MyTogether[DeltaF[gS,s,towerIn]+gR-g]===0];
Return[{gS,gR}];
];


Clear[SimpleRReduction]
SimpleRReduction[g_,f_,tower_?MatrixQ]:=Module[{t=tower[[-1,1]],a=tower[[-1,2]],s,mu,m,d,lambda,AAA,p,gCoeffs,gProj,i,gS,iPrime,k,u,v,towerMu,gR},
Assert[tower[[-1,3]]===0];
lambda=(t/.(Rule@@@TowerInfo["R-Extension"]));Assert[IntegerQ[lambda]];
m=Exponent[f,t];
s=Coefficient[f,t,m];
Assert[MyTogether[f-s t^m]===0];
d=GCD[lambda,m];
(*Print["d=  ",d];*)
mu=lambda/d;
p[i_,k_]:=p[i,k]=MyTogether[Product[MyTSigma[s a^i,l,tower],{l,0,k-1}]Product[Product[MyTSigma[ a^m,l,tower],{l,0,ll-1}],{ll,1,k-1}]];
gCoeffs=CoefficientList[MyTogether[g] ,t];
Assert[Length[gCoeffs]<=lambda];
gProj=PadRight[gCoeffs[[;;UpTo[d]]],d];
gS=0;
Do[
u=gCoeffs[[+1+i]];
iPrime=Mod[i,d];
k=MyExtendedGCD[m,lambda,iPrime-i][[1]];
gS+=-Sum[MyTSigma[u,j,tower]p[i,j]t^(i+j m),{j,0,k-1}];
gProj[[+1+iPrime]]+=MyTSigma[u,k,tower]p[i,k];
,{i,d,Length[gCoeffs]-1}];
Assert[MyTogether[DeltaF[gS,f,tower]+Sum[gProj[[+1+i]]t^i,{i,0,d-1}]-g]===0];

towerMu=If[mu>1,MyTogether[MyChangeShiftTower[tower[[;;-2]],mu]],tower[[;;-2]]];
Do[
v=gProj[[+1+i]];
{u,gProj[[+1+i]]}=RingReduction[v,p[i,mu],towerMu];
gS+=Sum[MyTSigma[u,j,tower]p[i,j]t^(i+j m),{j,0,mu-1}];
,{i,0,d-1}];
gR=Sum[gProj[[+1+i]]t^i,{i,0,d-1}];
(*Print[{gS,f,tower,gR,g}];*)
Assert[MyTogether[DeltaF[gS,f,tower]+gR-g]===0];
Return[{gS,gR}];

];



Clear[MyExtendedGCD];
MyExtendedGCD[a_,b_,c_]:=Module[{g,ag,bg,aC,bC},
Assert[Divisible[c, GCD[a,b]]];
{g,{ag,bg}}=ExtendedGCD[a,b];
{aC,bC}={ag,bg}*c/g;
{k,aC}=QuotientRemainder[aC,b];
bC+=a k;
Assert[aC a+bC b===c];
Assert[0<=aC<b];
Return[{aC,bC}]
]


(* ::Subsection::Closed:: *)
(*Idempotent*)


Clear[Project];
Project[f_,a_List,k_List,y_List]:=With[{alphas=Table[((-1)^(2/a[[i]]))^(a[[i]]-1-k[[i]]),{i,1,Length[y]}]},
	MyTogether[f/.Thread[Rule[y,alphas]]]]//ToRadicals


Clear[e];
e[l_List,k_List,y_List]:=Product[e[l[[i]],k[[i]],y[[i]]],{i,Length[l]}]
e[l_,kIn_,y_]:=e[l,Mod[kIn,l],y]=Module[{j,k=Mod[kIn,l]},(Times@@Drop[Table[y-((-1)^(2/l))^j,{j,0,l-1}],{l-1-k+1}])
/(Times@@Drop[Table[((-1)^(2/l))^(l-1-k)-((-1)^(2/l))^j,{j,0,l-1}],{l-1-k+1}])//RootReduce//ToRadicals];


Clear[MyChangeShiftTower]; 
MyChangeShiftTower[expr__]:=
(Sigma`DifferenceFields`BasicTools`DFInterface`ChangeShiftTower[expr]/.Sigma`Algebra`CompAlgSigma`II->I);


Clear[RemoveRMonomials];
RemoveRMonomials::NotAnRExtension="Error: Tower `1` extends the constants";
RemoveRMonomials::malformedTower="Error: Tower `1` is malformed or does not fit to list of R-monomials to remove";
RemoveRMonomials[tower_?MatrixQ,yList_List]:=Module[{curOrd,ordList,alphasProj,newtower},
ordList={};
newtower=tower;
Do[
	If[!MemberQ[yList,tower[[i,1]]],Continue[]];
	curOrd=MyGetOrderOfUnity[newtower[[i,2]]];
	If[curOrd==1,Message[RemoveRMonomials::NotAnRExtension,tower];Abort[]];
	 newtower=MyChangeShiftTower[newtower,curOrd];
	newtower[[;;,2;;]]=(newtower[[;;,2;;]]/.tower[[i,1]]->1);
	AppendTo[ordList,curOrd];
,{i,Length[tower]}];
newtower[[;;,2;;]]=MyTogether[newtower[[;;,2;;]]];
 newtower=Select[newtower,(Rest[#]=!={1,0})&];
If[Length[newtower]+Length[yList]!=Length[tower],
Message[RemoveRMonomials::malformedTower,tower];Abort[]];
Return[{newtower,ordList}];
]


(*Clear[IdempotentReduction];
IdempotentReduction::NotRExtension="No R-monomial in tower `1`"
IdempotentReduction[g_,f:1,tower_?MatrixQ]:=Module[{ordList,fm,numR,orders,gm,yList,newtower,ord,gS,gR,gSn,gRn},
If[!KeyExistsQ[TowerInfo["R-Extension"]],Message[IdempotentReduction::NotRExtension,tower];Abort[];];
Sow[Timing[
numR=Length[TowerInfo["R-Extension"][[;;,1]]\[Intersection] tower[[;;,1]]];
{yList,orders}=Transpose[TowerInfo["R-Extension"][[;;numR]]];
{newtower,ordList}=RemoveRMonomials[tower,yList];
ord=Times@@ordList;
gS=-Sum[Sum[MyTSigma[e[orders,orders-1,yList],j,tower],{j,k+1,ord-1}]MyTSigma[g,k,tower],{k,0,ord-1}];
(*Print[{gS,e[orders,orders-1,yList]Sum[MyTSigma[g,k,tower],{k,0,ord-1}]}];*)

gm=Sum[MyTSigma[g,k,tower]/.Thread[yList->1],{k,0,ord-1}];
Assert[CheckReduction[{g,f},{gS,e[orders,orders-1,yList]Sum[MyTSigma[g,k,tower],{k,0,ord-1}]},tower]];
fm=1;
(*Print[newtower];*)
{gSn,gRn}=RingReduction[gm,fm,newtower];
gR=e[orders,orders-1,yList]gRn;
gS+=Sum[MyTSigma[e[orders,orders-1,yList]gSn,k,tower],{k,0,ord-1}];
][[1]],"IdempotentReduction"];
Assert[CheckReduction[{g,f},{gS,gR},tower]];
Return[{gS,gR}];
]*)


(* ::Subsection:: *)
(*Creative/Parametric Teleskoping *)


Clear[FindSummableCombination]
FindSummableCombination[SigmaPairList_?MatrixQ,nonConsts_List]:=Module[{commonDen,R,c,m,B,i,j,Sol,n,sol},
R=SigmaPairList[[;;,2]];
n=Length[SigmaPairList];
If[MatchQ[R,{0..}],Return[Table[{sol,sol . SigmaPairList[[;;,1]]},{sol,IdentityMatrix[n]}]]];
commonDen=PolynomialLCM@@Denominator/@R;
B=Flatten/@PadRight[CoefficientList[Table[Numerator[R[[i]]]Cancel[commonDen/Denominator[R[[i]]]],{i,n}],nonConsts]];
Sol=If[MatrixRankHeuristic[B]<n,NullSpace[Transpose[B]],{}];
If[Sol==={},Return[{}]];
(*{Sol,MyTogether[Sol . SigmaPairList[[1;;n,1]]]}*)
Return[Table[{sol,sol . SigmaPairList[[;;,1]]},{sol,Sol}]]
]


(* ::Code::Initialization:: *)
Clear[PT];
PT[tower_List,F_List]:= Module[{n,A,R,c,clist,coeff,m,B,i,j,Sol},
n=Length[F];
ReInitTower[tower];
A=RingReduction[#,tower]&/@F;
A=MapAt[MyTogether,A,{All,2}];
Return[FindSummableCombination[A,tower[[;;,1]]]];
]



Clear[FindTeleskopingRecurrence]
FindTeleskopingRecurrence::norecfound="No recurrence of order <= `1` exists, increase value of option \"MaxOrder\"";

Options[FindTeleskopingRecurrence]={"MaxOrder"->30,"WithNegativeShifts"->False};
FindTeleskopingRecurrence[g_,{towerN_List,towerK_List},opts:OptionsPattern[]]:=FindTeleskopingRecurrence[g,{towerN,towerK},OptionValue["WithNegativeShifts"],opts]
FindTeleskopingRecurrence[g_,{towerN_List,towerK_List},False,OptionsPattern[]]:=Module[{comb,gPairList,m,gmS,gmR},
gPairList={};
ReInitTower[towerK];
{gmS,gmR}={0,0};
Do[
	{gmS,gmR}=RingReduction[If[m==0,g,MyTSigma[gmR,towerN]],towerK]+{MyTSigma[gmS,towerN],0};
	gmR=MyTogether[gmR];(* for FindSummableCombination it should be together*)
	Assert[MyTogether[DeltaF[gmS,1,towerK]+gmR-MyTSigma[g,m,towerN]]===0];
	AppendTo[gPairList,{gmS,gmR}];
	Sow[Timing[
	comb=FindSummableCombination[gPairList,towerK[[;;,1]]];
	][[1]],"FindSummableCombination"];
	If[comb=!={},Assert[MyTogether[Sum[comb[[1,1,i]]MyTSigma[g,i-1,towerN],{i,Length[comb[[1,1]]]}]-DeltaF[comb[[1,-1]],1,towerK]]===0];Break[]];
	(*Print["m:",m," New Remainder: ",gmR];*)
,{m,0,OptionValue["MaxOrder"]}];
If[comb==={},Message[FindTeleskopingRecurrence::norecfound,OptionValue["MaxOrder"]]];
Return[comb[[1]]];
]

FindTeleskopingRecurrence[g_,{towerN_List,towerK_List},True,OptionsPattern[]]:=Module[{result,comb,gPairList,m,gmS,gmR,shift,sign,lastP},
gPairList={};
ReInitTower[towerK];
{gmS,gmR}={0,0};
lastP={0,g};
Do[
	sign=If[EvenQ[m],-1,1];
	shift=sign Ceiling[m/2];
	{gmS,gmR}=RingReduction[If[m==0,g,MyTSigma[lastP[[2]],sign,towerN]],towerK]+{MyTSigma[lastP[[1]],sign,towerN],0};
	gmR=MyTogether[gmR];(* for FindSummableCombination it should be together*)
	Assert[MyTogether[DeltaF[gmS,1,towerK]+gmR-MyTSigma[g,shift,towerN]]===0];
	If[sign>0,AppendTo[gPairList,{gmS,gmR}],PrependTo[gPairList,{gmS,gmR}]];
	Sow[Timing[
	comb=FindSummableCombination[gPairList,towerK[[;;,1]]];
	][[1]],"FindSummableCombination"];
	If[comb=!={},
		result=MyTSigma[comb[[1]],Floor[m/2],towerN];
		result[[1]]=MyTogether[result[[1]]];
		Assert[MyTogether[Sum[result[[1,i]]MyTSigma[g,i-1,towerN],{i,Length[result[[1]]]}]-DeltaF[result[[-1]],1,towerK]]===0];
		Break[]
	];
	lastP=gPairList[[sign]];
	(*Print["m:",m," New Remainder: ",gmR];*)
,{m,0,OptionValue["MaxOrder"]}];
If[comb==={},Message[FindTeleskopingRecurrence::norecfound,OptionValue["MaxOrder"]]];
Return[result];
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
{g,u}=RingReduction[lc,tower1];
q+= g*t^d;
r+= u*t^d;
pt=Collect[pt-MyTSigma[g*t^d,1,tower]+g*t^d-u*t^d,t,MyTogether];
Assert[Exponent[pt,t]<d];
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
Assert[KeyExistsQ[TowerInfo,t]];
H=TowerInfo[t];
lt=H[[1]];
v0=H[[2]];
L=H[[5]];
m=Length[L];
Do[
	a=t^(i+1)/(i+1)-lt*t^i;
	b=MyTSigma[a,1,tower]-a-v0*t^i;
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
	{g,r}=RingReduction[tower[[i,3]],G];
	{b,c}=Rational`BasisElement[tower[[1;;i-1,1]],r];
	B={{tower[[i,1]]-g,r}};
	AppendTo[TowerInfo,{g,r,b,c,B}];
];
TowerInfo=AssociationThread[tower[[2;;,1]]->TowerInfo]
]


(* ::Subsection::Closed:: *)
(*Field stuff (not used)*)


(* ::Input::Initialization:: *)
(*Input: n, a positive integer
         DenomSeq is set to be a list consisting of n empty lists
*)


(* ::Input::Initialization:: *)
ResetDenomSeq[n_Integer]:=Module[{},
DenomSeq=Table[{},n]
];


(* ::Input::Initialization:: *)
(* Input: Two polynomials v, p in \Sigma tower with deg(v)<deg(p) and l an integer. *)
(* Output: {g, h} such that
v/\[Sigma]^l(p)=\[CapitalDelta](g)+h/p. *)
LocalNormalReduction[v_,p_,l_Integer,tower_List]:=Module[{i,g, h},
   If[l===0,Return[{0,v}]];
If[ l>0, g=Sum[MyTSigma[v,-i,tower]/MyTSigma[p,l-i,tower],{i,1,l}],g=Sum[-MyTSigma[v,i,tower]/MyTSigma[p,l+i,tower],{i,0,-l-1}]];
h=MyTSigma[v,-l,tower];
{g,h}];


(* ::Input::Initialization:: *)
(*Input: a \Sigma tower reperensted by{{x,1,1},{t_1,a_1,b_1},{t_2,a_2,b_2},...{t_n,a_n,b_n}},
        a nonzero {t_n}-proper element h in the tower, 
  Output: {g,h} such that f= \[CapitalDelta](g)+h, where g,h are in the tower and h is t-simple
*)


(* ::Input::Initialization:: *)
$activateEcho=False;
NormalReduction[f_,tower_List]:=Module[{ff=MyTogether[f],denf,deg,numf,t,A,n,B,L,i,j,w,C,d,m,g,k, R,h,time1,time2,time3,time4},
If[ff===0,Return[{0,0}]];
t=tower[[-1]][[1]];
denf=Denominator[ff];
denf=Cancel[denf/Coefficient[denf,t,Exponent[denf,t]]];
numf=Collect[denf*ff,{t},MyTogether];
time1=TimeUsed[];
A=GetCoprimeFactorization[denf,tower];
(*myEcho[TimeUsed[]-time1,"factor"];*)
n= Length[A[[1]]];
B ={};
L={};
time2=TimeUsed[];
Do[
m=Length[A[[2]][[1]][[3]][[i]]];
Do[
w=MyTSigma[A[[1]][[i]]^A[[2]][[1]][[3]][[i]][[j]][[2]],A[[2]][[1]][[3]][[i]][[j]][[1]],tower];

L=AppendTo[L,{A[[1]][[i]]^A[[2]][[1]][[3]][[i]][[j]][[2]],A[[2]][[1]][[3]][[i]][[j]][[1]]}];
B=AppendTo[B,w],{j,1,m}],
{i,1,n} 
];
(*myEcho[TimeUsed[]-time2,"set"];*)
time3=TimeUsed[];
C=Rational`ParFracDecomp[numf,B,t];
(*myEcho[TimeUsed[]-time3,"parFrac"];*)
g=0;
h=0;
time4=TimeUsed[];
Do[
R=LocalNormalReduction[C[[k]],L[[k]][[1]],L[[k]][[2]],tower];
g=g+R[[1]];
h=h+R[[2]]/L[[k]][[1]],
{k,1,Length[C]}
];  
(*myEcho[TimeUsed[]-time4,"Reduce"];*)
{g,h}
];



$activateEcho=False;
GetCoprimeFactorization[p_,tower_List]:=Module[{A,n,i,k,S,j,B},
A=Sigma`DifferenceFields`BasicTools`DFInterface`GetSigmaFactorization[{p},tower];
n=Length[A[[1]]];
k=Length[tower];
For [i=1,i<=n,i++,
S=SearchDenomSeq[k,A[[1]][[i]],tower];
If[S===Null,
	UpdateDenomSeq[k,A[[1]][[i]]]
,
	A[[1,i]]=S[[1]];
	B=A[[2]][[1]][[3]][[i]];
	For [j=1,j<=Length[B],j++,
		B[[j]][[1]]=B[[j]][[1]]+S[[2]];
		A[[2,1,3,i,j,1]]=B[[j,1]];
	];
];
];
A
];


(* ::Input::Initialization:: *)
(*Input: k, a positive integer,
         a \PiSigma tower C(x)(t_1,t_2,...,t_k)
         p,a monic and irreducible polynomial in t_k 
 Output: {m, q}, the Specification of p if there exists q such that \[Sigma]^m(q)=p,
           Otherwise, Null is returned
*)
SearchDenomSeq[k_Integer,p_,tower_List]:=Module[{M,m,i,a},
M=DenomSeq[[k]];
m=Length[M];
For[i=1,i<=m,i++,  a=Sigma`DifferenceFields`BasicTools`DFInterface`GetSpecification[M[[i]],p,tower];
 If[a=!=Null,Break[] ];
];
If[i==m+1,Return[],Return[{M[[i]],a}]]
];


(* ::Input::Initialization:: *)
(*Input: k, a positive integer no more than the length of DenomSeq,
         a, a member to be inserted in DenomSeq
*)
UpdateDenomSeq[k_Integer,a_]:=Module[{n, M},
n=Length[DenomSeq];
M=AppendTo[DenomSeq[[k]],a];
DenomSeq=ReplacePart[DenomSeq,k->M]
];


(* ::Input::Initialization:: *)
(*Input: a difference field (C(x),\[Sigma]) with \[Sigma](x)=x+1 and f in the field
Output: {g,h} such that
      f=\[CapitalDelta](g)+h,
            where g, h \in C(x) and h is x-simple
*)


(* ::Input::Initialization:: *)
$activateEcho=False;
CompleteReduction0[f_,var_Symbol]:=Module[{fp,pp,g,A},
{fp,pp}=Rational`ProperAndPolynomialParts[f,var];
g=Sum[pp,var];
A =NormalReduction[fp,{{var,1,1}}];
{g+A[[1]],A[[2]]}
];



(* ::Subsection:: *)
(*End of package*)


(* ::Input::Initialization:: *)
End[];


(* ::Input::Initialization:: *)
EndPackage[];
