(* ::Package:: *)

(* ::Input::Initialization:: *)
BeginPackage["RationalReduction`"];


ClearAll@@Names["RationalReduction`*"];


(* ::Input::Initialization:: *)
RationalReduction::usage=""


(* ::Input::Initialization:: *)
Begin["`Private`"];


(* ::Subsection:: *)
(*MISC*)


$activateJEcho=False;
Clear[JEcho];
JEcho[strings___,arg_]:=If[$activateJEcho,If[Length[{strings}]>0,Print[strings]];Echo[arg],arg]


Clear[MyTSigma]
MyTSigma[expr_,0,___]:=expr
MyTSigma[expr_,rest__]:=If[Variables[expr]==={},expr,Sigma`DifferenceFields`BasicTools`DFInterface`TSigma[expr,rest,False]]/.Sigma`Algebra`CompAlgSigma`II->I;


Clear[DeltaF];
DeltaF[g_,f_,tower_]:=f MyTSigma[g,1,tower]-g


Clear[MyEliminateRootObjects];
MyEliminateRootObjects[f_]:=If[FreeQ[f,Power[_,Rational[_,_]]|Root[__]],f,ToRadicals[RootReduce[Together[f]]]]


(*Nothing for QQ,
plain Together for QQ(x_1,x_2,...),
MyEliminateRootObjects for algebraic numbers 
(Mathematica is really bad at dealing with algebraic numbers like (-1)^(2/3))
*)
Clear[MyTogether]
MyTogether[f_]:=
If[!FreeQ[f,Power[_,Rational[_,_]]|Root[__]],
	Together[MyEliminateRootObjects[f]]
,If[Length[Variables[f]]>0,
	Together[f]
,
	f
]]


(*wwwaaayyy sslloowweerr*)
Clear[MyTaylorShiftList];
MyTaylorShiftList[g_List,k_Integer]:=Module[{i,l},
	Table[g[[i]]+Sum[g[[l]]Binomial[l-1,i-1]k^(l-i),{l,i+1,Length[g]}],{i,Length[g]}]]


Clear[MyGetSpecification]
MyGetSpecification[gIn_,f_,tower:{{x_,1,1}}]:=Module[{shiftListNumber,lc,g,i,l,k,dg=Exponent[gIn,x],df=Exponent[f,x]},
If[dg!=df,Return[Null]];
lc=Coefficient[f,x,df];
g=gIn*lc/Coefficient[gIn,x,dg];
k=MyTogether[(Coefficient[f,x,df-1]-Coefficient[g,x,dg-1])/(dg lc)];
shiftListNumber=5;
If[!IntegerQ[k],Return[Null]];
Do[
 If[MyTogether[Coefficient[g,x,i]+Sum[Coefficient[g,x,l]Binomial[l,i]k^(l-i),{l,i+1,dg}]-Coefficient[f,x,i]]=!=0,
 k=Null;
 Break[];
 ]
,{i,dg-2,Max[dg-shiftListNumber,0],-1}];
If[k=!=Null && shiftListNumber<dg && MyTogether[MyTSigma[g,k,tower]-f]=!=0,
	k=Null;
];
Return[k];
]


Clear[MyGetSigmaFactorization];
MyGetSigmaFactorization[{f_},tower:{{x_,1,1}}]:=Module[
{shiftgoal,factors={},lc,factorsRawDeg,sigmafactors={},sigmafactorsDeg,facTest,mult,degree,facNum,k,i,j,factorsDeg,factord,factorsRaw,xFreePart,fac},
factorsRaw=FactorList[f];
factorsRaw=Table[{fac[[1]],fac[[2]],Exponent[fac[[1]],x]},{fac,factorsRaw}];
factorsRaw=GatherBy[factorsRaw,Last];
xFreePart=Times@@(factorsRaw[[1,;;,1]]^factorsRaw[[1,;;,2]]);
Do[
	factorsDeg={};
	sigmafactorsDeg={};
	Do[		
		k=Null;
		{facTest,mult,degree}=factorsRawDeg[[i]];
		lc=Coefficient[facTest,x,degree];
		xFreePart*=lc^mult;
		Do[
			k=MyGetSpecification[factorsDeg[[j]],facTest,tower];
			If[k=!=Null,facNum=j;Break[];];
		,{j,Length[factorsDeg]}];
		If[k===Null,
			AppendTo[factorsDeg,MyTogether[facTest/lc]];
			AppendTo[sigmafactorsDeg,{{0,mult}}];
		,
			AppendTo[sigmafactorsDeg[[facNum]],{k,mult}];
		];
	,{i,Length[factorsRawDeg]}];
	factors=Join[factors,factorsDeg];
	sigmafactors=Join[sigmafactors,sigmafactorsDeg];
,{factorsRawDeg,Select[factorsRaw,(#[[1,3]]>0)&]}];
(*sigmafactors=(Total/@GatherBy[#,First])&/@sigmafactors;*)
(*Shift do the middle*)
shiftgoal=Floor/@Mean/@sigmafactors[[;;,;;,1]];
Do[sigmafactors[[i,;;,1]]-=shiftgoal[[i]],{i,Length[factors]}];
factors=Table[If[shiftgoal[[i]]!=0,MyTogether[MyTSigma[factors[[i]],shiftgoal[[i]],tower]],factors[[i]]],{i,Length[factors]}];
Assert[MyTogether[xFreePart Product[MyTSigma[factors[[i]],sigmafactors[[i,j,1]],tower]^sigmafactors[[i,j,2]] ,{i,Length[factors]},{j,Length[sigmafactors[[i]]]}]-f]===0];
Return[{factors,{{xFreePart,1,sigmafactors}}}];
]


Clear[LookupShiftEq]
LookupShiftEq[g_,CurrentS_List,tower_]:=Module[{key=Missing[],f,k},
Do[
	k=MyGetSpecification[g,f,tower];
	Assert[k===Sigma`DifferenceFields`BasicTools`DFInterface`GetSpecification[g,f,tower]];
	If[k=!=Null,
		key=f;
		Break[];
	]
,{f,CurrentS}];
If[Head[key]===Missing,Return[key],Return[k]];
]


Clear[AdjustSigmaFactorization]
AdjustSigmaFactorization[sigmaFactorization_,CurrentS_List,tower_List]:=Module[{NewS={},factors,sigmafac,i,k},
{factors,sigmafac}=sigmaFactorization;
Do[
Sow[Timing[
k=LookupShiftEq[factors[[i]],CurrentS,tower];
][[1]],"LookupShiftEq"];
If[Head[k]===Missing,
	AppendTo[NewS,factors[[i]]];
,
	factors[[i]]=MyTogether[MyTSigma[factors[[i]],k,tower]];
	sigmafac[[1,-1,i,;;,1]]-=k;
]
,{i,Length[factors]}];

Return[{{factors,sigmafac},Join[CurrentS,NewS]}];
]


(* ::Subsection:: *)
(*Rational Reduction*)


(*Ported to Mathematica from (HypergeometricCT.mm by Hui Huang) *)
Clear[PolynomialReduction]
PolynomialReduction[0,u_,v_,tower_]:={0,0}
PolynomialReduction[b_,u_,v_,tower:{{x_,_,_}}]:=Module[{du,dv,dp,lu,lv,a=0,p=b,d,i,g,pg,lp,cu,cv,m,bm,pm,r,gr,dr,lr,pr},
{du,dv,dp}=Exponent[{u,v,p},x];
lu=Coefficient[u,x,du];lv=Coefficient[v,x,dv];
Assert[PolynomialQ[b,x]];Assert[PolynomialQ[u,x]];Assert[PolynomialQ[v,x]];
If[du!=dv || MyTogether[lu-lv]=!=0, (*Case I*)
	d=Max[du,dv];
	If[du<dv,lu=0,If[du>dv,lv=0]];
	i=dp-d;
	While[i>=0,
		g=x^i/(lu-lv);
		pg=u MyTSigma[g,tower]-v g;
		lp=Coefficient[p,x,dp];
		a+=lp g;
		p=Collect[p-lp pg,x,Together];
		dp=Exponent[p,x];
		Assert[i>dp-d];
		i=dp-d;
	];
	Return[{a,p}];
,If[du==0,(*Case II*)
	i=dp+1;
	While[i>0,
		g=x^i/(i u);
		pg=Collect[((x+1)^i-x^i)/i, x,MyTogether];
		lp=Coefficient[p,x,dp];
		a+=lp g;
		p=Collect[p-lp pg, x,MyTogether];
		dp=Exponent[p,x];
		Assert[i>dp+1];
		i=dp+1;
	];
	Return[{a,p}];	
];];
{cu,cv}=Coefficient[{u,v},x,du-1];
m=MyTogether[(cv-cu)/lu];
If[IntegerQ[m]&&m>=0 ,  (*Case IV*)
	bm=Coefficient[b,x,du+m-1] x^(du+m-1);
	p=Collect[p-bm, x,MyTogether];
	dp=Exponent[p,x];
	i=dp-du+1;
	While[i>=0,
		g=x^i/(i lu+cu-cv);
		pg=Collect[u MyTSigma[g,tower]-v g, x,MyTogether];
		lp=Coefficient[p,x,dp];
		a+=lp g;
		p=Collect[p-lp pg, x,MyTogether] ;
		pm=Coefficient[p,x,du+m-1]x^(du+m-1);
		bm+=pm;
		p=Collect[p-pm, x,MyTogether];
		dp=Exponent[p,x];
		Assert[i>dp-du+1];
		i=dp-du+1;
	];
	
	r=Collect[u (x+1)^m-v x^m, x,MyTogether];
	gr=x^m;
	dr=Exponent[r,x];
	i=dr-du+1;
	While[i>=0,
		g=Coefficient[r,x,dr]x^i/(i lu+cu+cv);
		gr-=g;
		r=Collect[r-u MyTSigma[g,tower]+v g, x,MyTogether];	
		dr=Exponent[r,x];
		Assert[i>dr-du+1];
		i=dr-du+1;	
	];
	{lr,pr}=Coefficient[{r,p},x,dr];
	{a,p}={a+pr gr/lr,Collect[p+bm-pr r/lr, x,MyTogether]};
, (*Case III*)
	i=dp-du+1;
	While[i>=0,
		g=x^i/(i lu + cu-cv);
		pg=Collect[u MyTSigma[g,tower]-v g, x,MyTogether];
		lp=Coefficient[p,x,dp];
		a+=lp g;
		p=Collect[p-lp pg, x,MyTogether];
		dp=Exponent[p,x];
		Assert[i>dp-du+1];
		i=dp-du+1;	
	];
];
Return[{a,p}];
]


Clear[RationalRNF]
Options[RationalRNF]={"Representatives"->{}};
RationalRNF[f_,tower_List,OptionsPattern[]]:=Module[{CurrentS,factors,sigmaFac,shiftgoal={},multi,xi,eta,k,i,NewS={}},
CurrentS=OptionValue["Representatives"];
Sow[Timing[
{factors,sigmaFac}=MyGetSigmaFactorization[{f},tower];
][[1]],"MySigmaFactorization"];
shiftgoal=Table[0,{Length[factors]}];
Do[
multi=Total[sigmaFac[[1,-1,i,;;,2]]];
If[multi==0,Continue[]];
Sow[Timing[
	k=LookupShiftEq[factors[[i]],CurrentS,tower];
][[1]],"LookupShiftEq"];
If[Head[k]===Missing,	
	AppendTo[NewS,MyTogether[MyTSigma[factors[[i]],If[multi>0,1,-1],tower]]];
	shiftgoal[[i]]=0;
,
	shiftgoal[[i]]=If[multi>0,k-1,k+1];
]
,{i,Length[factors]}];
xi=MyTogether[sigmaFac[[1,1]]Product[MyTSigma[factors[[i]],shiftgoal[[i]],tower]^Total[sigmaFac[[1,-1,i,;;,2]]],{i,Length[factors]}]];
JEcho["xi:",xi];
eta=Product[Product[MyTSigma[factors[[i]],j,tower]^-Total[Select[sigmaFac[[1,-1,i]],(#[[1]]<=j)&][[;;,2]]],{j,Min[sigmaFac[[1,-1,i,;;,1]]],shiftgoal[[i]]-1}] ,{i,Length[factors]}]
	Product[Product[MyTSigma[factors[[i]],j-1,tower]^Total[Select[sigmaFac[[1,-1,i]],(#[[1]]>=j)&][[;;,2]]],{j,Max[sigmaFac[[1,-1,i,;;,1]]],shiftgoal[[i]]+1,-1}] ,{i,Length[factors]}];
JEcho["eta:",eta];
Assert[MyTogether[(xi MyTSigma[eta,tower]/eta-f)]===0];
Return[{{xi,eta},Join[CurrentS,NewS]}];
]


Clear[ShiftDenominatorToS];
ShiftDenominatorToS[gNum_,dks_,0,xi_,tower_List]:={0,gNum,0}
ShiftDenominatorToS[c_,dks_,l_Integer,K_,tower_]:=Module[{a,u,v,x=tower[[1,1]],s,t,fTilde,dksM1,gTilde,bTilde,dksP1,g0,result},
Assert[PolynomialQ[c,x]];Assert[PolynomialQ[dks,x]];
{u,v}=NumeratorDenominator[K];
If[l>0,
	{s,t}=ExtendedEuclidean[u,dks,v c,x];
	If[s===0,
		result={0,0,t}; (*i.e. fTilde===0*)
	,
		dksM1=MyTogether[MyTSigma[dks,-1,tower]];
		{gTilde,a,bTilde}=ShiftDenominatorToS[MyTSigma[s,-1,tower],dksM1,l-1,K,tower];
		(*<-- There might be theoretically some cancellation in MyTSigma[s,-1,tower]/dksM1 *)
		result={MyTSigma[s,-1,tower]/dksM1+gTilde,a,t+bTilde};
	];
,
	{s,t}=ExtendedEuclidean[v,MyTSigma[dks,1,tower],u MyTSigma[c,1,tower],x];
	g0=-c/dks;
	If[s===0,
		result={g0,0,t}; (*i.e. fTilde===0*)
	,
		dksP1=MyTogether[MyTSigma[dks,1,tower]];
		{gTilde,a,bTilde}=ShiftDenominatorToS[s,dksP1,l+1,K,tower];
		(*<-- There might be theoretically some cancellation in s/dksP1 *)
		result={g0+gTilde,a,t+bTilde};
	];		
];
Assert[MyTogether[c/dks -(DeltaF[result[[1]],K,tower]+result[[2]]/MyTSigma[dks,-l,tower]+result[[3]]/v)]===0];
Return[result];
]


Clear[ProperReduction]
Options[ProperReduction]={"Representatives"->{}};
ProperReduction[0,_,_,OptionsPattern[]]:={{0,0,0},OptionValue["Representatives"]}
ProperReduction[h_,xi_,tower:{{x_,1,1}},OptionsPattern[]]:=Module[{unsigmaFac,CurrentS,hNum,hDen, piSigmaMList,giSigmaNumList,xiDen,gijNumList,gijDenList,piList,hFac,maxPower,a,i,j,mij,u,v,aj,uj,vj,ai,ui,vi},
CurrentS=OptionValue["Representatives"];
{hNum,hDen}=NumeratorDenominator[h];
xiDen=Denominator[xi];
Sow[Timing[
unsigmaFac=MyGetSigmaFactorization[{hDen},tower];
][[1]],"MySigmaFactorization"];
{{piList,hFac},CurrentS}=AdjustSigmaFactorization[unsigmaFac,CurrentS,tower];

{hNum,hDen}/=hFac[[1,1]];
piSigmaMList=Table[Product[MyTSigma[piList[[i]],hFac[[1,-1,i,j,1]],tower]^hFac[[1,-1,i,j,2]],{j,Length[hFac[[1,-1,i]]]}],{i,Length[piList]}];
Sow[Timing[
giSigmaNumList=ParFracDecomp[hNum, piSigmaMList,x];
][[1]],"ParFracDecomp"];
Assert[MyTogether[Total[giSigmaNumList/piSigmaMList]-hNum/(Times@@piSigmaMList)]===0];
{a,u,v}={0,0,0};
Do[
	gijDenList=Table[MyTSigma[piList[[i]],hFac[[1,-1,i,j,1]],tower]^hFac[[1,-1,i,j,2]],{j,Length[hFac[[1,-1,i]]]}];
	Sow[Timing[
	gijNumList=ParFracDecompAlt[giSigmaNumList[[i]],gijDenList ,x];
	][[1]],"ParFracDecomp"];
	maxPower=Max[hFac[[1,-1,i,;;,2]]];
	{ai,ui,vi}={0,0,0};
	Do[
		mij=hFac[[1,-1,i,j,2]];
		Sow[Timing[
		{aj,uj,vj}=ShiftDenominatorToS[gijNumList[[j]],gijDenList[[j]],hFac[[1,-1,i,j,1]],xi,tower];
		][[1]],"ShiftDenominatorToS"];
		Assert[PolynomialQ[uj,x]];
		{ai,ui,vi}+={aj,uj*(piList[[i]]^(maxPower-mij)),vj};
	,{j,Length[gijNumList]}];
	{a,u,v}+={ai,ui/piList[[i]]^maxPower,vi};
,{i,Length[piList]}];
Assert[MyTogether[DeltaF[a,xi,tower]+u+v/xiDen -h]===0];
Return[{{a,u,v},CurrentS}];
]


Clear[LookupMultInFac];
LookupMultInFac[fac_?MatrixQ,k_Integer]:=Lookup[Association[Rule@@@fac],k,0]


Clear[ProperReductionAlt]
Options[ProperReductionAlt]={"Representatives"->{}};
ProperReductionAlt[0,_,_,OptionsPattern[]]:={{0,0,0},OptionValue["Representatives"]}
ProperReductionAlt[h_,xi_,tower:{{x_,1,1}},OptionsPattern[]]:=Module[{minShift,maxShift,unsigmaFac,CurrentS,hNum,hDen, piSigmaMList,giSigmaNumList,xiDen,piList,hFac,a,i,mij,u,v,ai,ui,vi},
CurrentS=OptionValue["Representatives"];
{hNum,hDen}=NumeratorDenominator[h];
xiDen=Denominator[xi];
Sow[Timing[
unsigmaFac=MyGetSigmaFactorization[{hDen},tower];
][[1]],"MySigmaFactorization"];
{{piList,hFac},CurrentS}=AdjustSigmaFactorization[unsigmaFac,CurrentS,tower];
{minShift,maxShift}=MinMax[hFac[[1,-1,;;,;;,1]]];
(*Print[{minShift,maxShift}];*)
piSigmaMList=Table[Product[MyTSigma[piList[[i]],k,tower]^LookupMultInFac[hFac[[1,-1,i]],k],{i,Length[piList]}],{k,minShift,maxShift}];
(*Print["{hFac[[1,1]], piSigmaMList}= ",{hFac[[1,1]], piSigmaMList}];*)
Sow[Timing[
giSigmaNumList=ParFracDecompAlt[hNum, piSigmaMList,x];
][[1]],"ParFracDecomp"];
Assert[MyTogether[Total[giSigmaNumList/piSigmaMList]-hNum/(Times@@piSigmaMList)]===0];
{a,u,v}={0,0,0};
Do[
	Sow[Timing[
	{ai,ui,vi}=ShiftDenominatorToS[giSigmaNumList[[k-minShift+1]],piSigmaMList[[k-minShift+1]],k,xi,tower];
	][[1]],"ShiftDenominatorToS"];
	Assert[PolynomialQ[ui,x]];
	{a,u,v}+={ai/hFac[[1,1]],ui/Product[piList[[i]]^LookupMultInFac[hFac[[1,-1,i]],k],{i,Length[piList]}]/hFac[[1,1]],vi/hFac[[1,1]]};
,{k,minShift,maxShift}];
Assert[MyTogether[DeltaF[a,xi,tower]+u+v/xiDen -h]===0];
Return[{{a,u,v},CurrentS}];
]


Clear[RationalReductionRNF]
Options[RationalReductionRNF]={"Representatives"->{}};
RationalReductionRNF[g_,xi_,tower:{{x_,_,_}},OptionsPattern[]]:=Module[{a,u,v,CurrentS,gT,h,hNum,hDen,mij,xiNum,xiDen,gTS,gTR,polyPair,properPair},
CurrentS=OptionValue["Representatives"];
Sow[Timing[
{xiNum,xiDen}=NumeratorDenominator[xi];
{h,gT}=JEcho["ProperAndPolynomialParts: ",ProperAndPolynomialPartsAlt[g,x]];
{hNum,hDen}=NumeratorDenominator[h];
][[1]],"ProperAndPolynomialParts"];
Sow[Timing[
{{a,u,v},CurrentS}=JEcho["ProperReduction: ",ProperReductionAlt[h,xi,tower,"Representatives"->CurrentS]];
][[1]],"ProperReduction"];
Sow[Timing[
{gTS,gTR}=JEcho["PolynomialReduction: ",PolynomialReduction[Collect[xiDen gT+v,x,MyTogether],xiNum,xiDen,tower]];
][[1]],"PolynomialReduction"];
Assert[MyTogether[DeltaF[gTS,xi,tower]+gTR/xiDen-(gT+v/xiDen)]===0];
Return[{{a+gTS,u+gTR/xiDen},CurrentS}];
]


Clear[RationalReduction]
Options[RationalReduction]={"Representatives"->{}};
RationalReduction[g_,f_,tower_,OptionsPattern[]]:=Module[{xi,eta,CurrentS,gS,gR},
Sow[Timing[
{{xi,eta},CurrentS}=RationalRNF[f,tower,"Representatives"->OptionValue["Representatives"]];
][[1]],"RationalRNF"];
{{gS,gR},CurrentS}=RationalReductionRNF[eta g,xi,tower,"Representatives"->CurrentS];
Return[{MyTogether[{eta^(-1)gS,eta^(-1)gR}],CurrentS}]
]





(* ::Subsection:: *)
(*Rational*)


(* ::Input::Initialization:: *)
Clear[ProperAndPolynomialParts];
ProperAndPolynomialParts[f_,var_Symbol]:=Module[{num,den,r,pp,fp},
{num,den}=NumeratorDenominator[MyTogether[f]];
{pp,r}=PolynomialQuotientRemainder[num,den,var];
Return[{r/den,pp}]
];


Clear[MyPolynomialQuotientRemainder];
MyPolynomialQuotientRemainder[pol_,div_,x_]:=
If[Length[Variables[{div}]]>1,
	Flatten[PolynomialReduce[pol,{div},{x}]] , PolynomialQuotientRemainder[pol,div,x]]



Clear[ProperAndPolynomialPartsAlt];
ProperAndPolynomialPartsAlt[f_,var_Symbol]:=Module[{rNum,rDen,num,den,r,pp,fp},
{num,den}=NumeratorDenominator[MyTogether[f]];
Sow[Timing[
{pp,r}=MyTogether[MyPolynomialQuotientRemainder[num,den,var]];
][[1]],"MyPolynomialQuotientRemainder"];
{rNum,rDen}=NumeratorDenominator[r];
Assert[PolynomialQ[pp,var]];
Assert[Exponent[rNum,var]<Exponent[rDen den,var]];
Assert[MyTogether[rNum/(rDen den)+pp-f]===0];
Return[{rNum/(rDen den),pp}]
];


(* Input: Two rational functions a and b which are polynomials in the variable var. *)
(* Output: The monic gcd of the numerators of a and b with respect to var. *)
Clear[Euclidean];
Euclidean[a_,b_,var_Symbol]:=Module[{g},
(* Observe that we are taking the GCD of their numerators (which are polynomials). *)
g=PolynomialGCD@@({a,b}//MyTogether//Numerator);
(* The main difference in this function compared to PolynomialGCD is that we make the gcd monic with respect to the desired variable. *)
g=Cancel[g/Coefficient[g,var,Exponent[g,var]]]
];


(* Input: Three polynomials a, b and c in var. *)
(* Output: Two polynomials r and s such that r a + s b = c and degree of r in var is lower than that of b. *)
Clear[ExtendedEuclidean]
ExtendedEuclidean[a_,b_,c_,var_Symbol]:=Module[{a1=MyTogether[a],b1=MyTogether[b],c1=MyTogether[c],g,r,s,h,r1,rem,q},
{g,{r,s}}=PolynomialExtendedGCD[a1,b1,var];
{h,rem}=MyPolynomialQuotientRemainder[c1,g,var];
If[rem=!=0,Throw["Error in ExtendedEuclidean: c is not in the ideal generated by a and b."]];
{r,s}=MyTogether[h {r,s}];
(* In this case we take care to keep track of the main variable to give the correct output in terms of the main variable. *)
If[!(r===0)&&Exponent[b1,var]<= Exponent[r,var],
	(* An ad hoc trick: we only compute the quotient and remainder of the numerators in order to save time (because we know that it is a polynomial in terms of var). *)
	{q,r1}=MyPolynomialQuotientRemainder[Numerator[r],Numerator[b1],var];
	(* We remember to return the denominator here! *)
	s=MyTogether[q a1 Denominator[b1]/Denominator[r]+s];
	{r1/Denominator[r],s}
,
	{r,s}
]
];



Clear[ExtendedEuclideanAlt]
ExtendedEuclideanAlt[a_,b_,c_,var_Symbol]:=Module[{s1,a1=MyTogether[a],b1=MyTogether[b],c1=MyTogether[c],g,r,s,h,r1,rem,q},
{g,{r,s}}=PolynomialExtendedGCD[a1,b1,var];
{h,rem}=MyPolynomialQuotientRemainder[c1,g,var];
If[rem=!=0,Throw["Error in ExtendedEuclidean: c is not in the ideal generated by a and b."]];
{r,s}=MyTogether[h {r,s}];
(* In this case we take care to keep track of the main variable to give the correct output in terms of the main variable. *)
If[!(r===0)&&Exponent[b1,var]<= Exponent[r,var],
	(* An ad hoc trick: we only compute the quotient and remainder of the numerators in order to save time (because we know that it is a polynomial in terms of var). *)
	{q,r1}=MyPolynomialQuotientRemainder[Numerator[r],Numerator[b1],var];
	(* We remember to return the denominator here! *)
	s=MyTogether[q a1 Denominator[b1]/Denominator[r]+s];
	{r,s}={r1/Denominator[r],s};
];
If[!(s===0)&&Exponent[a1,var]<= Exponent[s,var],
	(* An ad hoc trick: we only compute the quotient and remainder of the numerators in order to save time (because we know that it is a polynomial in terms of var). *)
	{q,s1}=MyPolynomialQuotientRemainder[Numerator[s],Numerator[a1],var];
	(* We remember to return the denominator here! *)
	r=MyTogether[q b1 Denominator[a1]/Denominator[s]+r];
	{s,r}={s1/Denominator[s],r};
];
Return[{r,s}];
]


(*Input: a, a polynomial in K[y];
        [d_1,...,d_m], a list of polynomials in K[y] with
         deg(a)<deg(d_1*d_2...*d_m)
       deg(d_i)>0 and gcd(d_i,d_j)=1 for i<>j;
  Output:{a_1,a_2,...,a_m}, where a_i is a polynomial with deg(a_i)<deg(d_i) and gcd(a_i,d_i)=1
        such that a/(d_1*...*d_m)=a_1/d_1+...a_m/d_m.
*)
Clear[ParFracDecomp]
ParFracDecomp[a_, T_List,y_]:= Module[{n,a1,s,t,W},
 n=Length[T];
If[n===1, Return[MyTogether[{a}]]];
t= Product[T[[i]],{i,2,n}];
{a1,s}=ExtendedEuclidean[t,T[[1]],a,y];
W = ParFracDecomp[s,T[[2;;]],y];
Return[Prepend[W, a1]];
];


Clear[ParFracDecompAlt]
ParFracDecompAlt[a_, T_List,y_]:= Module[{i,n,a1,s,t,V,W,t1,t2,a2},
n=Length[T];
If[n==1, Return[MyTogether[{a}]]];
t1= Product[T[[i]],{i,Floor[n/2]}];
t2= Product[T[[i]],{i,Floor[n/2]+1,n}];
{a1,a2}=ExtendedEuclideanAlt[t1,t2,a,y];
V = ParFracDecompAlt[a2,T[[;;Floor[n/2]]],y];
W = ParFracDecompAlt[a1,T[[Floor[n/2]+1;;]],y];
Return[Join[V,W]];
];


(* ::Input::Initialization:: *)
(*Input: a,b, two polynomials that has only normal factors in a \PiSigma tower,
  Output: the dispersion set of a,b     
*)


(* ::Input::Initialization:: *)
$activateEcho=True;
Clear[myEcho];
myEcho[args___]:=If[$activateEcho,Echo[args]];
Clear[DispersionSet]
DispersionSet[a_,b_,tower_List]:=Module[{t,A,B,DS,i,j,s,m},
t=tower[[-1]][[1]];
(*trivial case*)
 If [Exponent[a,t]===0||Exponent[b,t]===0, Return[{}]];
  (*obtain all irreducible factors of a and b,respectively*)
A=FactorList[FactorTermsList[a,t][[-1]]];
A=Drop[#[[1]]&/@A,1];
A=Numerator[A];
B=FactorList[FactorTermsList[b,t][[-1]]];
B=Drop[#[[1]]&/@B,1];
B=Numerator[B];
myEcho[{A,B},"{A,B}:"];
(*find the dispersion set*)
DS={};
For[i=1,i<=Length[A],i++,
For[j=1,j<=Length[B],j++,
s=-Sigma`DifferenceFields`BasicTools`DFInterface`GetSpecification[A[[i]],B[[j]],tower];
 If  [s=!=Null,DS=Union[DS,{s}]];
];
];
DS
];


(* ::Input::Initialization:: *)
$activateEcho=True;
Clear[myEcho];
myEcho[args___]:=If[$activateEcho,Echo[args]];

Clear[RNF]
RNF[f_,tower_List]:=Module[{ff=MyTogether[f],t,nf,df,A,c,u,v,s,r},
(*trivial case*)
t=tower[[-1]][[1]];
If[FreeQ[ff,t],Return[{f,1,1,1}]];
(*Compute an RNF of the primitive part*)
A=FactorTermsList[#,t]&/@NumeratorDenominator[ff];
myEcho[{A},"{A}:"];
c=ff*A[[2]][[-1]]/A[[1]][[-1]];
myEcho[{c},"{c}:"];
{u,v,s,r}=PrimitiveRNF[A[[1]][[-1]],A[[2]][[-1]],tower];
myEcho[{u,v,s,r},"{u,v,s,r}:"];
u=MyTogether[Cancel[c*u/v]];
{Numerator[u],Denominator[u],s,r}
];


(* ::Input::Initialization:: *)
$activateEcho=True;
Clear[myEcho];
myEcho[args___]:=If[$activateEcho,Echo[args]];
Clear[PrimitiveRNF];
PrimitiveRNF[nf_,df_,tower_List]:=Module[{w1,w2,u,v,s,r,t, DS,pDS,nDS,i,k,p,pk},
(*trivial case*)
{w1,w2}={1,1};
{u, v,s, r}={nf,df,1,1};
t =tower[[-1]][[1]];
If [Exponent[u,t]===0 || Exponent[v,t]===0,Return[{u,v,s,r}]];
(*handle with special factors in the \Pi case*)
If[tower[[-1]][[3]]===0, 
   If[PolynomialRemainder[u,t,t]===0,
u=u/t;
w1=w1*t
];
If[PolynomialRemainder[v,t,t]===0,
v=v/t;
w2=w2*t
];
];
 (*Compute the dispersion set of u and v*)
myEcho[{u,w1,v,w2},"{u,w1,v,w2}:"];
DS=DispersionSet[u,v,tower];
myEcho[{DS},"{DS}:"];
pDS =Select[DS,Positive];
nDS=Select[DS, Negative];
myEcho[{pDS,nDS},"{pDS,nDS}:"];
(*deal with Positive integers*)
For[i=1,i<=Length[pDS],i++,
    k=pDS[[i]];
         p=Euclidean[u,Sigma`DifferenceFields`BasicTools`DFInterface`TSigma[v,k,tower],t];
       pk=Sigma`DifferenceFields`BasicTools`DFInterface`TSigma[p,-k,tower];
    {u,v}={Cancel[u/p],Cancel[v/pk]};       s=s*Product[Sigma`DifferenceFields`BasicTools`DFInterface`TSigma[p,j,tower],{j,1,k-1}]*pk;
myEcho[{p,pk,s},"{p,pk,s}:"];
];
(*deal with negative integers*)
For[i=1,i<=Length[nDS],i++,
    k=nDS[[i]];
         p=Euclidean[u,Sigma`DifferenceFields`BasicTools`DFInterface`TSigma[v,k,tower],t];
       pk=Sigma`DifferenceFields`BasicTools`DFInterface`TSigma[p,-k,tower];
    {u,v}={Cancel[u/p],Cancel[v/pk]};       r=r*Product[Sigma`DifferenceFields`BasicTools`DFInterface`TSigma[p,j,tower],{j,0,-k-1}];
];
{u*w1,v*w2,s,r}
];


(* ::Subsection:: *)
(*End of package*)


End[];
EndPackage[];
