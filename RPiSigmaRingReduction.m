(* ::Package:: *)

 


$activateEcho=True;
Clear[JEcho];
JEcho[args___]:=If[$activateEcho,Echo[args],args]


Clear[MyTSigma]
MyTSigma[expr_,0,___]:=expr
MyTSigma[expr_,rest__]:=If[Variables[expr]==={},expr,Sigma`DifferenceFields`BasicTools`DFInterface`TSigma[expr,rest,False]]/.Sigma`Algebra`CompAlgSigma`II->I;


Clear[RationalReduction]
RationalReduction[g_,f_,tower_]:=Module[{xi,eta,rnf},
rnf=RNF[f,tower];
{xi,eta}={rnf[[1]]/rnf[[2]],rnf[[3]]/rnf[[4]]};

Return[eta^(-1) RationalReductionRNF[eta g,xi,tower]]
]


Clear[RationalReductionRNF]
Options[RationalReductionRNF]={"Representatives"->{}};
RationalReductionRNF[g_,xi_,tower_,OptionsPattern[]]:=Module[{CurrentS, gT,h,x=tower[[-1,1]],hNum,hDen,piList,hFac,piSigmaMList,giSigmaNumList,
																pijList,maxPower,mij,a,u,v,aj,uj,vj,xiNum,xiDen},
CurrentS=OptionValue["Representatives"];
{h,gT}=ProperAndPolynomialParts[g,x];
If[h===0,Return[]];
{hNum,hDen}=NumeratorDenominator[h];
{xiNum,xiDen}=NumeratorDenominator[xi];
{{piList,hFac},CurrentS}=AdjustSigmaFactorization[GetSigmaFactorization[{hDen},tower],CurrentS,tower];
{hNum,hDen}/=hFac[[1,1]];
piSigmaMList=Table[Product[MyTSigma[piList[[i]],hFac[[1,-1,i,j,1]],tower]^hFac[[1,-1,i,j,2]],{j,Length[hFac[[1,-1,i]]]}],{i,Length[piList]}];
giSigmaNumList=ParFracDecomp[JEcho[hNum], JEcho[piSigmaMList],x];

{a,u,v}={0,0,0};
Do[
	pijList=ParFracDecomp[giSigmaNumList[[i]], Table[MyTSigma[piList[[i]],hFac[[1,-1,i,j,1]],tower]^hFac[[1,-1,i,j,2]],{j,Length[hFac[[1,-1,i]]]}],x];
	maxPower=Max[hFac[[1,-1,i,;;,2]]];
	Do[
		mij=hFac[[1,-1,i,j,2]];
		{aj,uj,vj}=ShiftDenominatorToS[pijList[[j]],piList[[i]]^mij,hFac[[1,-1,i,j,1]],xi,tower];
		{a,u,v}+={aj,u*(pijList[[j]]^(maxPower-mij)),vj};
	,{j,Length[pijList]}];
,{i,Length[piList]}];
Return[{{a,u/hDen+gT+v/xiDen},CurrentS}];
]


Clear[DeltaF];
DeltaF[g_,f_,tower_]:=f MyTSigma[g,1,tower]-g


g=1/(x+1);f=(x^2+4);
RationalReductionRNF[DeltaF[g,f,tower],f,tower]
Together[%]


tower={{x,1,1}};
{piList,hFac}=GetSigmaFactorization[{x (x+1)^2(2x+1)},{{x,1,1}}]


AdjustSigmaFactorization[{piList,hFac},{2x+5},tower]


LookupShiftEq[x,{7x+4,7x-4},tower]


Clear[LookupShiftEq]
LookupShiftEq[g_,CurrentS_List,tower]:=Module[{key=Missing[],f,k},
Do[
	k=Sigma`DifferenceFields`BasicTools`DFInterface`GetSpecification[g,f,tower];
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
k=LookupShiftEq[factors[[i]],CurrentS,tower];
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
ShiftDenominatorToS[gNum_,dks_,0,xi_,tower_]:={0,gNum,0}
ShiftDenominatorToS[c_,dks_,l_Integer,K_,tower_]:=Module[{a,u,v,x=tower[[1,1]],s,t,fTilde,dksM1,gTilde,bTilde,dksP1,g0},
Assert[PolynomialQ[c,x]];Assert[PolynomialQ[dks,x]];Assert[PolynomialQ[K,x]];
{u,v}=NumeratorDenominator[K];
If[l>0,
	{s,t}=ExtendedEuclidean[u,dks,v c,x];
	If[s===0,
		Return[{0,0,t}]; (*i.e. fTilde===0*)
	,
		dksM1=Together[MyTSigma[dks,-1,tower]];
		{gTilde,a,bTilde}=ShiftDenominatorToS[MyTSigma[s,-1,tower],dksM1,l-1,K,tower];
		(*<-- There might be theoretically some cancellation in MyTSigma[s,-1,tower]/dksM1 *)
		Return[{MyTSigma[s,-1,tower]/dksM1+gTilde,a,t+bTilde}];
	];
,
	{s,t}=ExtendedEuclidean[v,MyTSigma[dks,1,tower],u MyTSigma[c,1,tower],x];
	g0=-c/dks;
	If[s===0,
		Return[{g0,0,t}]; (*i.e. fTilde===0*)
	,
		dksP1=Together[MyTSigma[dks,1,tower]];
		{gTilde,a,bTilde}=ShiftDenominatorToS[s,dksP1,l+1,K,tower];
		(*<-- There might be theoretically some cancellation in s/dksP1 *)
		Return[{g0+gTilde,a,t+bTilde}];
	];
,
		
];
Return[{a,u,v}];
]


(*Clear[NormalForm]
NormalForm[f_,tower_]:=Module[{xi,eta},

Return[{xi,eta}]
]*)


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
