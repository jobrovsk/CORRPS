(* ::Package:: *)

(* ::Section:: *)
(*Code*)


$activateEcho=True;
Clear[JEcho];
JEcho[strings___,arg_]:=If[$activateEcho,If[Length[{strings}]>0,Print[strings]];Echo[arg],arg]


Clear[MyTSigma]
MyTSigma[expr_,0,___]:=expr
MyTSigma[expr_,rest__]:=If[Variables[expr]==={},expr,Sigma`DifferenceFields`BasicTools`DFInterface`TSigma[expr,rest,False]]/.Sigma`Algebra`CompAlgSigma`II->I;


Clear[DeltaF];
DeltaF[g_,f_,tower_]:=f MyTSigma[g,1,tower]-g


(*Ported to Mathematica from (HypergeometricCT.mm by Hui Huang) *)
Clear[PolynomialReduction]
PolynomialReduction[0,u_,v_,tower_]:={0,0}
PolynomialReduction[b_,u_,v_,tower:{{x_,_,_}}]:=Module[{du,dv,dp,lu,lv,a=0,p=b,d,i,g,pg,lp,cu,cv,m,bm,pm,r,gr,dr,lr,pr},
{du,dv,dp}=Exponent[{u,v,p},x];
lu=Coefficient[u,x,du];lv=Coefficient[v,x,dv];
If[du!=dv || lu!=lv, (*Case I*)
	d=Max[du,dv];
	If[du<dv,lu=0,If[du>dv,lv=0]];
	i=dp-d;
	While[i>=0,
		g=x^i/(lu-lv);
		pg=u MyTSigma[g,tower]-v g;
		lp=Coefficient[p,x,dp];
		a+=lp g;
		p=Expand[p-lp pg];
		dp=Exponent[p,x];
		i=dp-d;
	];
	Return[{a,p}];
,If[du==0,(*Case II*)
	i=dp+1;
	While[i>0,
		g=x^i/(i u);
		pg=Together[((x+1)^i-x^i)/i];
		lp=Coefficient[p,x,dp];
		a+=lp g;
		p=Expand[p-lp pg];
		dp=Exponent[p,x];
		i=dp+1;
	];
	Return[{a,p}];	
];];
{cu,cv}=Coefficient[{u,v},x,du-1];
m=(cv-cu)/lu;
If[IntegerQ[m]&&m>=0 ,  (*Case IV*)
	bm=Coefficient[b,x,du+m-1] x^(du+m-1);
	p=Expand[p-bm];
	dp=Exponent[p,x];
	i=dp-du+1;
	While[i>=0,
		g=x^i/(i lu+cu-cv);
		pg=Expand[u MyTSigma[g,tower]-v g];
		lp=Coefficient[p,x,dp];
		a+=lp g;
		p=Expand[p-lp pg];
		pm=Coefficient[p,x,du+m-1]x^(du+m-1);
		bm+=pm;
		p=Expand[p-pm];
	
		dp=Exponent[p,x];
		i=dp-du+1;
	];
	
	r=Expand[u (x+1)^m-v x^m];
	gr=x^m;
	dr=Exponent[r,x];
	i=dr-du+1;
	While[i>=0,
		g=Coefficient[r,x,dr]x^i/(i lu+cu+cv);
		gr-=g;
		r=Expand[r-u MyTSigma[g,tower]+v g];	
		dr=Exponent[r,x];
		i=dr-du+1;	
	];
	{lr,pr}=Coefficient[{r,p},x,dr];
	{a,p}={a+pr gr/lr,Expand[p+bm-pr r/lr]};
, (*Case III*)
	i=dp-du+1;
	While[i>=0,
		g=x^i/(i lu + cu-cv);
		pg=Expand[u MyTSigma[g,tower]-v g];
		lp=Coefficient[p,x,dp];
		a+=lp g;
		p=Expand[p-lp pg];
		dp=Exponent[p,x];
		i=dp-du+1;	
	];
];
Return[{a,p}];
]


test=RandomInteger[10^2,{500}]/RandomInteger[10^4,{500}];
Timing[Variables[test];]
Timing[Total[test];]


(*wwwaaayyy sslloowweerr*)
Clear[MyTaylorShiftList];
MyTaylorShiftList[g_List,k_Integer]:=Module[{i,l},
	Table[g[[i]]+Sum[g[[l]]Binomial[l-1,i-1]k^(l-i),{l,i+1,Length[g]}],{i,Length[g]}]]


testpol=FromDigits[Reverse[test],x];
Timing[Expand[DiscreteShift[testpol,{x,5}]];]
Timing[Expand[MyTSigma[testpol,5,tower]];]
Timing[Expand[testpol/.x->x+5];]
Timing[MyTaylorShiftList[test,-5];]


Clear[MyGetSpecification]
MyGetSpecification[gIn_,f_,tower_:{{x_,1,1}}]:=Module[{lc,g,i,l,k,dg=Exponent[gIn,x],df=Exponent[f,x]},
If[dg!=df,Return[Null]];
lc=Coefficient[f,x,df];
g=gIn*lc/Coefficient[gIn,x,dg];
k=Together[(Coefficient[f,x,df-1]-Coefficient[g,x,dg-1])/(dg lc)];
If[!IntegerQ[k],Return[Null]];
Do[
 If[Together[Coefficient[g,x,i]+Sum[Coefficient[g,x,l]Binomial[l,i]k^(l-i),{l,i+1,dg}]-Coefficient[f,x,i]]=!=0,
 k=Null;
 Break[];
 ]
,{i,dg-2,Max[dg-3,0],-1}];
If[k=!=Null && Together[MyTSigma[g,k,tower]-f]=!=0,
	k=Null;
];
Return[k];
]


Clear[MyGetSigmaFactorization];
MyGetSigmaFactorization[{f_},tower:{{x_,1,1}}]:=Module[
{factors={},lc,factorsRawDeg,sigmafactors={},sigmafactorsDeg,facTest,mult,degree,facNum,k,i,j,factorsDeg,factord,factorsRaw,xFreePart,fac},
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
			AppendTo[factorsDeg,Together[facTest/lc]];
			AppendTo[sigmafactorsDeg,{{0,mult}}];
		,
			AppendTo[sigmafactorsDeg[[facNum]],{k,mult}];
		];
	,{i,Length[factorsRawDeg]}];
	factors=Join[factors,factorsDeg];
	sigmafactors=Join[sigmafactors,sigmafactorsDeg];
,{factorsRawDeg,Select[factorsRaw,(#[[1,3]]>0)&]}];
(*sigmafactors=(Total/@GatherBy[#,First])&/@sigmafactors;*)
Assert[Together[xFreePart Product[MyTSigma[factors[[i]],sigmafactors[[i,j,1]],tower]^sigmafactors[[i,j,2]] ,{i,Length[factors]},{j,Length[sigmafactors[[i]]]}]-f]===0];
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
	factors[[i]]=Together[MyTSigma[factors[[i]],k,tower]];
	sigmafac[[1,-1,i,;;,1]]-=k;
]
,{i,Length[factors]}];

Return[{{factors,sigmafac},Join[CurrentS,NewS]}];
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
		dksM1=Together[MyTSigma[dks,-1,tower]];
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
		dksP1=Together[MyTSigma[dks,1,tower]];
		{gTilde,a,bTilde}=ShiftDenominatorToS[s,dksP1,l+1,K,tower];
		(*<-- There might be theoretically some cancellation in s/dksP1 *)
		result={g0+gTilde,a,t+bTilde};
	];		
];
Assert[Together[c/dks -(DeltaF[result[[1]],K,tower]+result[[2]]/MyTSigma[dks,-l,tower]+result[[3]]/v)]===0];
Return[result];
]


Clear[RationalRNF]
Options[RationalRNF]={"Representatives"->{}};
RationalRNF[f_,tower_List,OptionsPattern[]]:=Module[{CurrentS,factors,sigmaFac,shiftgoal={},multi,xi,eta,k,i,NewS={}},
CurrentS=OptionValue["Representatives"];
{factors,sigmaFac}=MyGetSigmaFactorization[{f},tower];
shiftgoal=Table[0,{Length[factors]}];
Do[
multi=Total[sigmaFac[[1,-1,i,;;,2]]];
If[multi==0,Continue[]];
k=LookupShiftEq[factors[[i]],CurrentS,tower];
If[Head[k]===Missing,	
	AppendTo[NewS,Together[MyTSigma[factors[[i]],If[multi>0,1,-1],tower]]];
	shiftgoal[[i]]=0;
,
	shiftgoal[[i]]=If[multi>0,k-1,k+1];
]
,{i,Length[factors]}];
xi=sigmaFac[[1,1]]Product[MyTSigma[factors[[i]],shiftgoal[[i]],tower]^Total[sigmaFac[[1,-1,i,;;,2]]],{i,Length[factors]}];
JEcho["xi:",xi];
eta=Product[Product[MyTSigma[factors[[i]],j,tower]^-Total[Select[sigmaFac[[1,-1,i]],(#[[1]]<=j)&][[;;,2]]],{j,Min[sigmaFac[[1,-1,i,;;,1]]],shiftgoal[[i]]-1}] ,{i,Length[factors]}]
	Product[Product[MyTSigma[factors[[i]],j-1,tower]^Total[Select[sigmaFac[[1,-1,i]],(#[[1]]>=j)&][[;;,2]]],{j,Max[sigmaFac[[1,-1,i,;;,1]]],shiftgoal[[i]]+1,-1}] ,{i,Length[factors]}];
JEcho["eta:",eta];
Assert[Together[(xi MyTSigma[eta,tower]/eta-f)]===0];
Return[{{xi,eta},Join[CurrentS,NewS]}];
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
][[1]],"SigmaFactorization"];
{{piList,hFac},CurrentS}=AdjustSigmaFactorization[unsigmaFac,CurrentS,tower];

{hNum,hDen}/=hFac[[1,1]];
piSigmaMList=Table[Product[MyTSigma[piList[[i]],hFac[[1,-1,i,j,1]],tower]^hFac[[1,-1,i,j,2]],{j,Length[hFac[[1,-1,i]]]}],{i,Length[piList]}];
giSigmaNumList=ParFracDecomp[hNum, piSigmaMList,x];
Assert[Together[Total[giSigmaNumList/piSigmaMList]-hNum/(Times@@piSigmaMList)]===0];
{a,u,v}={0,0,0};
Do[
	gijDenList=Table[MyTSigma[piList[[i]],hFac[[1,-1,i,j,1]],tower]^hFac[[1,-1,i,j,2]],{j,Length[hFac[[1,-1,i]]]}];
	gijNumList=ParFracDecomp[giSigmaNumList[[i]],gijDenList ,x];
	maxPower=Max[hFac[[1,-1,i,;;,2]]];
	{ai,ui,vi}={0,0,0};
	Do[
		mij=hFac[[1,-1,i,j,2]];
		{aj,uj,vj}=ShiftDenominatorToS[gijNumList[[j]],gijDenList[[j]],hFac[[1,-1,i,j,1]],xi,tower];
		Assert[PolynomialQ[uj,x]];
		{ai,ui,vi}+={aj,uj*(piList[[i]]^(maxPower-mij)),vj};
	,{j,Length[gijNumList]}];
	{a,u,v}+={ai,Expand[ui]/piList[[i]]^maxPower,vi};
,{i,Length[piList]}];
Assert[Together[DeltaF[a,xi,tower]+u+v/xiDen -h]===0];
Return[{{a,u,v},CurrentS}];
]


Clear[RationalReductionRNF]
Options[RationalReductionRNF]={"Representatives"->{}};
RationalReductionRNF[g_,xi_,tower:{{x_,_,_}},OptionsPattern[]]:=Module[{a,u,v,CurrentS,gT,h,hNum,hDen,mij,xiNum,xiDen,gTS,gTR,polyPair,properPair},
CurrentS=OptionValue["Representatives"];
Sow[Timing[
{xiNum,xiDen}=NumeratorDenominator[xi];
{h,gT}=JEcho["ProperAndPolynomialParts: ",ProperAndPolynomialParts[g,x]];
{hNum,hDen}=NumeratorDenominator[h];
][[1]],"ProperAndPolynomialParts"];
Sow[Timing[
{{a,u,v},CurrentS}=JEcho["ProperReduction: ",ProperReduction[h,xi,tower,"Representatives"->CurrentS]];
][[1]],"ProperReduction"];
Sow[Timing[
{gTS,gTR}=JEcho["PolynomialReduction: ",PolynomialReduction[Expand[xiDen gT+v],xiNum,xiDen,tower]];
][[1]],"PolynomialReduction"];
Assert[Together[DeltaF[gTS,xi,tower]+gTR/xiDen-(gT+v/xiDen)]===0];
Return[{{a+gTS,u+gTR/xiDen},CurrentS}];
]


Clear[RationalReduction]
Options[RationalReduction]={"Representatives"->{}};
RationalReduction[g_,f_,tower_,OptionsPattern[]]:=Module[{xi,eta,CurrentS,gS,gR},
Sow[Timing[
Sow[Timing[
{{xi,eta},CurrentS}=RationalRNF[f,tower,"Representatives"->OptionValue["Representatives"]];
][[1]],"RationalRNF"];
{{gS,gR},CurrentS}=RationalReductionRNF[eta g,xi,tower,"Representatives"->CurrentS];
][[1]],"RationalReductionCombined"];
Return[{Together[{eta^(-1)gS,eta^(-1)gR}],CurrentS}]
]


Clear[RingReduction]
Options[RingReduction]={"Representatives"->{}};
RingReduction[0,_,_?MatrixQ,OptionsPattern[]]:={{0,0},OptionValue["Representatives"]}
RingReduction[g_,f_,tower_?MatrixQ,OptionsPattern[]]:=Module[{alpha,beta,CurrentS,gS,gR},
CurrentS=OptionValue["Representatives"];
If[Length[tower]==1,
	Assert[tower[[1,2;;3]]==={1,1}];
	Return[RationalReduction[g,f,tower,"Representatives"->CurrentS]];	
];
{alpha,beta}=tower[[-1,2;;3]];
If[beta===0,
	If[RootOfUnityQ[alpha],
		Return[RReduction[g,f,tower,"Representatives"->CurrentS]];
	,
		Return[PiReduction[g,f,tower,"Representatives"->CurrentS]];
	];
];
If[alpha===1,
	Assert[f===1];
	Return[SigmaReduction[g,tower,"Representatives"->CurrentS]];
]
]


(* ::Subsection:: *)
(*Pi-Case*)


Clear[PiReduction];
Options[PiReduction]={"Representatives"->{}};
PiReduction[g_,s_,towerIn_?MatrixQ,OptionsPattern[]]:=Module[
{st,sc,i,degG,gS,gR,gcS,gcR,tdegG,gCoeffs,CurrentS,t,h,a,m,tower=Most[towerIn]},
CurrentS=OptionValue["Representatives"];
Assert[towerIn[[-1,3]]===0];
{t,a}=towerIn[[-1,1;;2]];
Assert[Exponent[s,t]==-Exponent[s,t^-1]];
m=Exponent[s,t];
tdegG=-Exponent[g,t^(-1)];
degG=Exponent[g,t];
gCoeffs=CoefficientList[g t^(-tdegG),t];
If[m==0,
	{gS,gR}=Sum[
		{{gcS,gcR},CurrentS}=RingReduction[gCoeffs[[i-tdegG+1]],s a^i,tower,"Representatives"->CurrentS];
		{gcS,gcR}t^i
	,{i,tdegG,degG}];
	Assert[Together[DeltaF[gS,s,towerIn]+gR-g]===0];
	Return[{{gS,gR},CurrentS}];
];
sc=(s/.t->1);
Print["g= ",g];
gCoeffs=PadRight[gCoeffs,Max[degG,Abs[m]-1]-Min[tdegG,0]+1,0,Max[tdegG,0]];
Print["gCoeffs= ",gCoeffs];
st=Min[tdegG,0]-1; (*exponent of first entry in gCoeffs*)
gS=0;
If[m>0,
	Do[
		gCoeffs[[i+m-st]]+=sc a^i MyTSigma[gCoeffs[[i-st]],tower];
		gS-=gCoeffs[[i-st]]t^i;	
	,{i,tdegG,-1}];
	Do[
		h=MyTSigma[gCoeffs[[i-st]]/(sc a^(i-m)),-1,tower];
		gCoeffs[[i-m-st]]+=h;
		gS+=h t^(i-m);	
	,{i,degG,m,-1}];
	
];
If[m<0,
	Do[
		h=MyTSigma[gCoeffs[[i-st]]/(sc a^(i-m)),-1,tower];
		gCoeffs[[i-m-st]]+=h;
		gS+=h t^(i-m);	
	,{i,tdegG,-1}];
	Do[
		gCoeffs[[i+m-st]]+=sc a^i MyTSigma[gCoeffs[[i-st]],tower];
		gS-=gCoeffs[[i-st]]t^i;	
	,{i,degG,-m,-1}];
];
gR=Sum[Together[gCoeffs[[i-st]]] t^i,{i,0,Abs[m]-1}];
Print[{m,gR//Factor}];
Assert[Together[DeltaF[gS,s,towerIn]+gR-g]===0];
Return[{{gS,gR},CurrentS}];
];


(* ::Subsection::Closed:: *)
(*Rational*)


(* ::Input::Initialization:: *)
Clear[ProperAndPolynomialParts];
ProperAndPolynomialParts[f_,var_Symbol]:=Module[{num,den,r,pp,fp},
{num,den}=NumeratorDenominator[Together[f]];
{pp,r}=PolynomialQuotientRemainder[num,den,var];
Return[{r/den,pp}]
];


(* ::Input::Initialization:: *)
(* Input: Two rational functions a and b which are polynomials in the variable var. *)
(* Output: The monic gcd of the numerators of a and b with respect to var. *)
Clear[Euclidean];
Euclidean[a_,b_,var_Symbol]:=Module[{g},
(* Observe that we are taking the GCD of their numerators (which are polynomials). *)
g=PolynomialGCD@@({a,b}//Together//Numerator);
(* The main difference in this function compared to PolynomialGCD is that we make the gcd monic with respect to the desired variable. *)
g=Cancel[g/Coefficient[g,var,Exponent[g,var]]]
];


(* ::Input::Initialization:: *)
(* Input: Three polynomials a, b and c in var. *)
(* Output: Two polynomials r and s such that r a + s b = c and degree of r in var is lower than that of b. *)
Clear[ExtendedEuclidean]
ExtendedEuclidean[a_,b_,c_,var_Symbol]:=Module[{a1=Together[a],b1=Together[b],c1=Together[c],g,r,s,h,r1,rem,q},
{g,{r,s}}=PolynomialExtendedGCD[a1,b1,var];
{h,rem}=PolynomialQuotientRemainder[c1,g,var];
If[rem=!=0,Throw["Error in ExtendedEuclidean: c is not in the ideal generated by a and b."]];
{r,s}=Cancel[h {r,s}];
(* In this case we take care to keep track of the main variable to give the correct output in terms of the main variable. *)
If[!(r===0)&&Exponent[b1,var]<= Exponent[r,var],
(* An ad hoc trick: we only compute the quotient and remainder of the numerators in order to save time (because we know that it is a polynomial in terms of var). *)
{q,r1}=PolynomialQuotientRemainder[Numerator[r],Numerator[b1],var];
(* We remember to return the denominator here! *)
s=Together[q a1 Denominator[b1]/Denominator[r]+s];
{r1/Denominator[r],s},
{r,s}]
];


(* ::Input::Initialization:: *)
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
If[n===1, Return[{a}]];
t= Product[T[[i]],{i,2,n}];
{a1,s}=ExtendedEuclidean[t,T[[1]],a,y];
W = ParFracDecomp[s,Drop[T,{1}] ,y];
Prepend[W, a1]
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
RNF[f_,tower_List]:=Module[{ff=Together[f],t,nf,df,A,c,u,v,s,r},
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
u=Together[Cancel[c*u/v]];
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


(* ::Section:: *)
(*Tests*)


timingsReduction={"ProperReduction","PolynomialReduction","SigmaFactorization","LookupShiftEq",
"ProperAndPolynomialParts","RationalRNF","RationalReductionCombined"};


Clear[randomPoly]
randomPoly[maxAnzahlMonome_Integer,maxDeg_Integer,maxCoef_,vars_List]:=Module[{res,numVars=Length[vars]},
res=Expand[Sum[(Times@@(vars^(RandomInteger[{0,maxDeg},{numVars}])))RandomInteger[{-maxCoef,maxCoef}] ,{i,0,RandomInteger[{1,maxAnzahlMonome}]}]];
If[res===0,Return[1],Return[res]];
]
Clear[randomPolyFactors]
randomPolyFactors[{numFactorsNum_Integer,numFactorsDen_Integer},maxAnzahlMonome_Integer,maxDeg_Integer,maxCoef_,vars_List]:=
Factor[Product[randomPoly[maxAnzahlMonome,maxDeg,maxCoef,vars],{numFactorsNum}]/Product[randomPoly[maxAnzahlMonome,maxDeg,maxCoef,vars],{numFactorsDen}]]


Clear[TestReduction];
TestReduction[{numFactorsNum_Integer,numFactorsDen_Integer},maxAnzahlMonome_Integer,maxDeg_Integer,maxCoef_]:=Module[
{h,zero,CurrentS,tower={{x,1,1}},dg,rg,dh,rh,f,g,dgh,rgh},
f=randomPolyFactors[{3,3},3,2,4,{x}];
g=randomPolyFactors[{numFactorsNum,numFactorsDen},maxAnzahlMonome,maxDeg,maxCoef,{x}];
h=randomPolyFactors[{numFactorsNum,numFactorsDen},maxAnzahlMonome,maxDeg,maxCoef,{x}];
TimeConstrained[
{{dg,rg},CurrentS}=RationalReduction[g,f,tower];
{{dh,rh},CurrentS}=RationalReduction[h,f,tower,"Representatives"->CurrentS];
{{dgh,rgh},CurrentS}=RationalReduction[g+h+DeltaF[zero,f,tower],f,tower,"Representatives"->CurrentS];
,10,Print["Time: ",{f,g,h}];Abort[]];
If[Together[rgh-rg-rh]=!=0,Print[{f,g,h}];Abort[]];
]


Clear[TestReduction];
TestReduction[{numFactorsNum_Integer,numFactorsDen_Integer},maxAnzahlMonome_Integer,maxDeg_Integer,maxCoef_]:=Module[
{h,zero,CurrentS,tower={{x,1,1}},dg,rg,dh,rh,f,g,dgh,rgh},
f=randomPolyFactors[{3,3},3,2,4,{x}];
g=randomPolyFactors[{numFactorsNum,numFactorsDen},maxAnzahlMonome,maxDeg,maxCoef,{x}]
	+randomPolyFactors[{numFactorsNum,0},maxAnzahlMonome,maxDeg,maxCoef,{x}];
h=randomPolyFactors[{numFactorsNum,numFactorsDen},maxAnzahlMonome,maxDeg,maxCoef,{x}]
	+randomPolyFactors[{numFactorsNum,0},maxAnzahlMonome,maxDeg,maxCoef,{x}];
TimeConstrained[
{{dg,rg},CurrentS}=RationalReduction[g,f,tower];
{{dh,rh},CurrentS}=RationalReduction[h,f,tower,"Representatives"->CurrentS];
{{dgh,rgh},CurrentS}=RationalReduction[g+h+DeltaF[zero,f,tower],f,tower,"Representatives"->CurrentS];
,10,Print["Time: ",{f,g,h}];Abort[]];
If[Together[rgh-rg-rh]=!=0,Print[{f,g,h}];Abort[]];
]


$activateEcho=False;


$activateEcho=True;


MyTSigma[-((896 x (1+x)^2 (2+x) (-3+x^2) (3+4 (1+x)) (3+(1+x)^2))/(-1+7 x^2))/((f/t) 2^3 ),-1,{{x,1,1}}]


SeedRandom[1837];
tower={{x,1,1},{t,x,0}};
f=randomPolyFactors[{3,3},3,2,4,{x}]/t^-0;
g=randomPolyFactors[{5,0},3,2,4,{x}]t^(-3)+t;
zero=DeltaF[g,f,tower];
Factor[zero]
Timing[RingReduction[zero,f,tower][[1]]]


SeedRandom[17837];
tower={{x,1,1}};
f=randomPolyFactors[{3,3},3,2,4,{x}];
g=randomPolyFactors[{5,5},3,2,4,{x}]+randomPolyFactors[{50,0},3,2,4,{x}];
zero=DeltaF[g,f,tower];
Timing[RingReduction[zero,f,tower][[1,2]]]
Timing[SolveDifferenceVectorSpace[{1,-f},{zero},tower];]
result=Timing[Reap[SolvePLDEInDRMaster[{{{1}},{{-f}}},{{zero}},tower],Join[timingsGeneral,Table[ToString[tower[[i,1]]]<>" combined",{i,Length[tower]}]]]];
SortBy[Transpose[{Join[timingsGeneral,Table[ToString[tower[[i,1]]]<>" combined",{i,Length[tower]}]],Total[#,2]&/@result[[2,2]]}],-#[[2]]&]


{f,g,zero}={(2 (-3+x) (-2+x) x (2+5 x^2))/((-1+x) (1+x) (2+3 x^2)),(3 (-1+x) (-1+2 x) (-3-3 x+2 x^2))/(x^3 (2+5 x) (2+x^2)),-((3 (-2+x)^2 x (1+x) (2+x)^2)/((-1+2 x) (1+2 x) (-2+x+2 x^2)))};
f=(2 (-3+x) (2+5 x^2))/(2+3 x^2);
{{dg,rg},CurrentS}=RationalReduction[g,f,tower];
{rg,CurrentS}[[1]]//Together
{{dgg,rgg},CurrentS}=RationalReduction[rg+DeltaF[zero,f,tower],f,tower,"Representatives"->CurrentS];
rgg//Together


SeedRandom[17837];
result=Timing[Reap[Do[TestReduction[{30,30},3,2,2],{100}],Join[timingsReduction,Table[ToString[tower[[i,1]]]<>" combined",{i,Length[tower]}]]]];
{result[[1]],result[[2,1]],SystemInformation["Kernel","MachineName"]}
SortBy[Transpose[{Join[timingsReduction,Table[ToString[tower[[i,1]]]<>" combined",{i,Length[tower]}]],Total[#,2]&/@result[[2,2]]}],-#[[2]]&]


Off[Assert];


On[Assert];


g=(4x^2+x+5);f=1/(x);
g=(4x^2+x+5);f=2x^2/(x^2-1)(x+5)/(x-5);
Timing[RationalReduction[DeltaF[g,f,tower],f,tower]]
(*Timing[RationalReductionRNF[DeltaF[g,f,tower],f,tower]]*)
Together[%[[2,1,2]]]


g=(x+5)/((x-1)x (2x+1)(x^2+1));f=(x-4);
Timing[RationalReductionRNF[DeltaF[g,f,tower],f,tower]]
Together[%]


tower={{x,1,1}};
{piList,hFac}=GetSigmaFactorization[{x (x+1)^2(2x+1)},{{x,1,1}}]


AdjustSigmaFactorization[{piList,hFac},{2x+5},tower]


LookupShiftEq[x,{7x+4,7x-4},tower]
