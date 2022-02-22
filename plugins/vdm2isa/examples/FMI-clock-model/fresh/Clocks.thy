(* VDM to Isabelle Translation @2022-02-22T09:21:43.169309Z
   Copyright 2021, Leo Freitas, leo.freitas@newcastle.ac.uk

in 'Clocks.vdmsl' at line 1:8
files = [Clocks.vdmsl]
*)
theory Clocks
imports "VDMToolkit" 
begin


\<comment>\<open>VDM source: Real1 = real
	inv r == (r >= 0)\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 35:5\<close>
type_synonym Real1 = "VDMReal"
	

\<comment>\<open>VDM source: inv_Real1: (real +> bool)
	inv_Real1(r) ==
(r >= 0)\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 36:9\<close>
definition
	inv_Real1 :: "Real1 \<Rightarrow> bool"
where
	"inv_Real1 r \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `inv_Real1` specification.\<close>
		(((inv_VDMReal r)))  \<and> 
		\<comment>\<open>User defined body of inv_Real1.\<close>
		(r \<ge> (0::VDMNat))"
 
lemmas inv_Real1_defs = inv_Real1_def inv_VDMReal_def 


	
	
\<comment>\<open>VDM source: Time = compose Time of r:Real1, i:nat end
	eq a = b == (((a.r) = (b.r)) and ((a.i) = (b.i)))
	ord a < b == (((a.r) < (b.r)) or (((a.r) = (b.r)) and ((a.i) < (b.i))))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 42:5\<close>
record Time = 
	r\<^sub>T\<^sub>i\<^sub>m\<^sub>e :: "Real1"
		 
		 i\<^sub>T\<^sub>i\<^sub>m\<^sub>e :: "VDMNat"
	

\<comment>\<open>VDM source: inv_Time: (Time +> bool)
	inv_Time(dummy0) ==
null\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 42:5\<close>
definition
	inv_Time :: "Time \<Rightarrow> bool"
where
	"inv_Time dummy0 \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `inv_Time` specification.\<close>
		( (((inv_Real1 (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e dummy0))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e dummy0))) ))"
 

\<comment>\<open>VDM source: eq_Time: (Time * Time +> bool)
	eq_Time(a, b) ==
(((a.r) = (b.r)) and ((a.i) = (b.i)))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 45:8\<close>
definition
	eq_Time :: "Time \<Rightarrow> Time \<Rightarrow> bool"
where
	"eq_Time a   b \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `eq_Time` specification.\<close>
		(inv_Time a  \<and>  inv_Time b)  \<and> 
		\<comment>\<open>User defined body of eq_Time.\<close>
		(((r\<^sub>T\<^sub>i\<^sub>m\<^sub>e a) = (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e b)) \<and> ((i\<^sub>T\<^sub>i\<^sub>m\<^sub>e a) = (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e b)))"
 

\<comment>\<open>VDM source: ord_Time: (Time * Time +> bool)
	ord_Time(a, b) ==
(((a.r) < (b.r)) or (((a.r) = (b.r)) and ((a.i) < (b.i))))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 46:9\<close>
definition
	ord_Time :: "Time \<Rightarrow> Time \<Rightarrow> bool"
where
	"ord_Time a   b \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `ord_Time` specification.\<close>
		(inv_Time a  \<and>  inv_Time b)  \<and> 
		\<comment>\<open>User defined body of ord_Time.\<close>
		(((r\<^sub>T\<^sub>i\<^sub>m\<^sub>e a) < (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e b)) \<or> (((r\<^sub>T\<^sub>i\<^sub>m\<^sub>e a) = (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e b)) \<and> ((i\<^sub>T\<^sub>i\<^sub>m\<^sub>e a) < (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e b))))"
 
lemmas inv_Time_defs = inv_Real1_def inv_Time_def inv_VDMNat_def inv_VDMReal_def 


	
	
\<comment>\<open>VDM source: Interval = (<calculated> | <changing> | <constant> | <countdown> | <fixed> | <triggered> | <tunable>)\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 52:5\<close>
datatype Interval = U_calculated  | 
		 U_changing  | 
		 U_constant  | 
		 U_countdown  | 
		 U_fixed  | 
		 U_triggered  | 
		 U_tunable 
	

\<comment>\<open>VDM source: inv_Interval: (Interval +> bool)
	inv_Interval(dummy0) ==
null\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 52:5\<close>
definition
	inv_Interval :: "Interval \<Rightarrow> bool"
where
	"inv_Interval dummy0 \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `inv_Interval` specification.\<close>
		((((inv_True dummy0))))"

		 
lemmas inv_Interval_defs = inv_Interval_def inv_True_def 


	
	
\<comment>\<open>VDM source: FMUMode = (<DONE> | <EVENT> | <INIT> | <STEP>)\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 54:5\<close>
datatype FMUMode = U_DONE  | 
		 U_EVENT  | 
		 U_INIT  | 
		 U_STEP 
	

\<comment>\<open>VDM source: inv_FMUMode: (FMUMode +> bool)
	inv_FMUMode(dummy0) ==
null\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 54:5\<close>
definition
	inv_FMUMode :: "FMUMode \<Rightarrow> bool"
where
	"inv_FMUMode dummy0 \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `inv_FMUMode` specification.\<close>
		((((inv_True dummy0))))"

		 
lemmas inv_FMUMode_defs = inv_FMUMode_def inv_True_def 


	
	
\<comment>\<open>VDM source: Contract = (<delayed> | <none> | <reactive>)\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 56:5\<close>
datatype Contract = U_delayed  | 
		 U_none  | 
		 U_reactive 
	

\<comment>\<open>VDM source: inv_Contract: (Contract +> bool)
	inv_Contract(dummy0) ==
null\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 56:5\<close>
definition
	inv_Contract :: "Contract \<Rightarrow> bool"
where
	"inv_Contract dummy0 \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `inv_Contract` specification.\<close>
		((((inv_True dummy0))))"

		 
lemmas inv_Contract_defs = inv_Contract_def inv_True_def 


	
	
\<comment>\<open>VDM source: RealNaN = (<NaN> | real)\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 58:5\<close>
datatype RealNaN = U_NaN  | 
		 U_VDMReal "VDMReal"
	

\<comment>\<open>VDM source: inv_RealNaN: (RealNaN +> bool)
	inv_RealNaN(dummy0) ==
null\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 58:5\<close>
definition
	inv_RealNaN :: "RealNaN \<Rightarrow> bool"
where
	"inv_RealNaN dummy0 \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `inv_RealNaN` specification.\<close>
		(((case dummy0 of
		 RealNaN.U_NaN  \<Rightarrow> (inv_True dummy0)
		  | RealNaN.U_VDMReal dummy0 \<Rightarrow> (inv_VDMReal dummy0)
		 )))"

		 
lemmas inv_RealNaN_defs = inv_RealNaN_def inv_True_def inv_VDMReal_def 


	
	
\<comment>\<open>VDM source: PortType = (<continous> | <discrete>)\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 60:5\<close>
datatype PortType = U_continous  | 
		 U_discrete 
	

\<comment>\<open>VDM source: inv_PortType: (PortType +> bool)
	inv_PortType(dummy0) ==
null\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 60:5\<close>
definition
	inv_PortType :: "PortType \<Rightarrow> bool"
where
	"inv_PortType dummy0 \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `inv_PortType` specification.\<close>
		((((inv_True dummy0))))"

		 
lemmas inv_PortType_defs = inv_PortType_def inv_True_def 


	
	
\<comment>\<open>VDM source: Causality = (<input> | <output>)\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 62:5\<close>
datatype Causality = U_input  | 
		 U_output 
	

\<comment>\<open>VDM source: inv_Causality: (Causality +> bool)
	inv_Causality(dummy0) ==
null\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 62:5\<close>
definition
	inv_Causality :: "Causality \<Rightarrow> bool"
where
	"inv_Causality dummy0 \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `inv_Causality` specification.\<close>
		((((inv_True dummy0))))"
 
lemmas inv_Causality_defs = inv_Causality_def inv_True_def 


	
	
\<comment>\<open>VDM source: ActionType = (<get> | <getC> | <set> | <setC> | <step>)\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 66:5\<close>
datatype ActionType = U_get  | 
		 U_getC  | 
		 U_set  | 
		 U_setC  | 
		 U_step 
	

\<comment>\<open>VDM source: inv_ActionType: (ActionType +> bool)
	inv_ActionType(dummy0) ==
null\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 66:5\<close>
definition
	inv_ActionType :: "ActionType \<Rightarrow> bool"
where
	"inv_ActionType dummy0 \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `inv_ActionType` specification.\<close>
		((((inv_True dummy0))))"

		 
lemmas inv_ActionType_defs = inv_ActionType_def inv_True_def 


	
	
\<comment>\<open>VDM source: ValueType = (bool | real)\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 68:5\<close>
datatype ValueType = U_bool "bool" | 
		 U_VDMReal "VDMReal"
	

\<comment>\<open>VDM source: inv_ValueType: (ValueType +> bool)
	inv_ValueType(dummy0) ==
null\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 68:5\<close>
definition
	inv_ValueType :: "ValueType \<Rightarrow> bool"
where
	"inv_ValueType dummy0 \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `inv_ValueType` specification.\<close>
		(((case dummy0 of
		 ValueType.U_bool dummy0 \<Rightarrow> (inv_bool dummy0)
		  | ValueType.U_VDMReal dummy0 \<Rightarrow> (inv_VDMReal dummy0)
		 )))"
 
lemmas inv_ValueType_defs = inv_VDMReal_def inv_ValueType_def inv_bool_def 


	
	
\<comment>\<open>VDM source: Name = seq1 of (char)\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 74:5\<close>
type_synonym Name = "VDMChar VDMSeq1"
	

\<comment>\<open>VDM source: inv_Name: (Name +> bool)
	inv_Name(dummy0) ==
null\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 74:5\<close>
definition
	inv_Name :: "Name \<Rightarrow> bool"
where
	"inv_Name dummy0 \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `inv_Name` specification.\<close>
		(((inv_VDMSeq1' (inv_VDMChar) dummy0)))"
 
lemmas inv_Name_defs = inv_Name_def inv_VDMChar_def inv_VDMSeq1'_def inv_VDMSeq1'_defs 


	
	
\<comment>\<open>VDM source: Ref = nat\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 79:5\<close>
type_synonym Ref = "VDMNat"
	

\<comment>\<open>VDM source: inv_Ref: (Ref +> bool)
	inv_Ref(dummy0) ==
null\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 79:5\<close>
definition
	inv_Ref :: "Ref \<Rightarrow> bool"
where
	"inv_Ref dummy0 \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `inv_Ref` specification.\<close>
		(((inv_VDMNat dummy0)))"
 
lemmas inv_Ref_defs = inv_Ref_def inv_VDMNat_def 


	
	
\<comment>\<open>VDM source: Action = compose Action of actionType:ActionType, fmu:Name, port:Ref end
	inv mk_Action(actionType, -, port) == ((actionType = <step>) <=> (port <> 0))
	eq act1 = act2 == (((act1.actionType) = (act2.actionType)) and (((act1.fmu) = (act2.fmu)) and ((act1.port) = (act2.port))))
	ord a < b == (((a.port) < (b.port)) or (((a.port) = (b.port)) and ((len (a.fmu)) < (len (b.fmu)))))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 84:5\<close>
record Action = 
	actionType\<^sub>A\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n :: "ActionType"
		 
		 fmu\<^sub>A\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n :: "Name"
		 
		 port\<^sub>A\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n :: "Ref"
	

\<comment>\<open>VDM source: inv_Action: (Action +> bool)
	inv_Action(mk_Action(actionType, -, port)) ==
((actionType = <step>) <=> (port <> 0))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 88:9\<close>
definition
	inv_Action :: "Action \<Rightarrow> bool"
where
	"inv_Action dummy0 \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `inv_Action` specification.\<close>
		( (((inv_ActionType (actionType\<^sub>A\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n dummy0))) \<and> 
		 ((inv_Name (fmu\<^sub>A\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n dummy0))) \<and> 
		 ((inv_Ref (port\<^sub>A\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n dummy0))) ))  \<and> 
		\<comment>\<open>Implicit pattern context conversion\<close>
		(let actionType = (actionType\<^sub>A\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n dummy0); dummy0_ignore = (fmu\<^sub>A\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n dummy0); port = (port\<^sub>A\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n dummy0) in 
		\<comment>\<open>User defined body of inv_Action.\<close>
		(
		\<comment>\<open>Implicit union type parameters projection\<close>
		(((actionType = ActionType.U_step ) \<longleftrightarrow> (port \<noteq> (0::VDMNat))))))"
 

\<comment>\<open>VDM source: eq_Action: (Action * Action +> bool)
	eq_Action(act1, act2) ==
(((act1.actionType) = (act2.actionType)) and (((act1.fmu) = (act2.fmu)) and ((act1.port) = (act2.port))))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 90:8\<close>
definition
	eq_Action :: "Action \<Rightarrow> Action \<Rightarrow> bool"
where
	"eq_Action act1   act2 \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `eq_Action` specification.\<close>
		(inv_Action act1  \<and>  inv_Action act2)  \<and> 
		\<comment>\<open>User defined body of eq_Action.\<close>
		(((actionType\<^sub>A\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n act1) = (actionType\<^sub>A\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n act2)) \<and> (((fmu\<^sub>A\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n act1) = (fmu\<^sub>A\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n act2)) \<and> ((port\<^sub>A\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n act1) = (port\<^sub>A\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n act2))))"
 

\<comment>\<open>VDM source: ord_Action: (Action * Action +> bool)
	ord_Action(a, b) ==
(((a.port) < (b.port)) or (((a.port) = (b.port)) and ((len (a.fmu)) < (len (b.fmu)))))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 94:9\<close>
definition
	ord_Action :: "Action \<Rightarrow> Action \<Rightarrow> bool"
where
	"ord_Action a   b \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `ord_Action` specification.\<close>
		(inv_Action a  \<and>  inv_Action b)  \<and> 
		\<comment>\<open>User defined body of ord_Action.\<close>
		(((port\<^sub>A\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n a) < (port\<^sub>A\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b)) \<or> (((port\<^sub>A\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n a) = (port\<^sub>A\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b)) \<and> ((len (fmu\<^sub>A\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n a)) < (len (fmu\<^sub>A\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b)))))"
 
lemmas inv_Action_defs = inv_Action_def inv_ActionType_def inv_Name_def inv_Ref_def inv_True_def inv_VDMChar_def inv_VDMNat_def inv_VDMSeq1'_def inv_VDMSeq1'_defs 


	
	
\<comment>\<open>VDM source: FMURef = compose FMURef of name:Name, ref:Ref end
	eq mk_FMURef(name1, ref1) = mk_FMURef(name2, ref2) == ((name1 = name2) and (ref1 = ref2))
	ord a < b == ((a.ref) < (b.ref))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 102:5\<close>
record FMURef = 
	name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f :: "Name"
		 
		 ref\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f :: "Ref"
	

\<comment>\<open>VDM source: inv_FMURef: (FMURef +> bool)
	inv_FMURef(dummy0) ==
null\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 102:5\<close>
definition
	inv_FMURef :: "FMURef \<Rightarrow> bool"
where
	"inv_FMURef dummy0 \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `inv_FMURef` specification.\<close>
		( (((inv_Name (name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f dummy0))) \<and> 
		 ((inv_Ref (ref\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f dummy0))) ))"

		 

\<comment>\<open>VDM source: eq_FMURef: (FMURef * FMURef +> bool)
	eq_FMURef(mk_FMURef(name1, ref1), mk_FMURef(name2, ref2)) ==
((name1 = name2) and (ref1 = ref2))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 105:8\<close>
definition
	eq_FMURef :: "FMURef \<Rightarrow> FMURef \<Rightarrow> bool"
where
	"eq_FMURef dummy0   dummy0 \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `eq_FMURef` specification.\<close>
		(inv_FMURef dummy0  \<and>  inv_FMURef dummy0)  \<and> 
		\<comment>\<open>Implicit pattern context conversion\<close>
		(let name1 = (name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f dummy0); ref1 = (ref\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f dummy0); 
			name1 = (name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f dummy0); ref1 = (ref\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f dummy0) in 
		\<comment>\<open>User defined body of eq_FMURef.\<close>
		((name1 = name2) \<and> (ref1 = ref2)))"

		 

\<comment>\<open>VDM source: ord_FMURef: (FMURef * FMURef +> bool)
	ord_FMURef(a, b) ==
((a.ref) < (b.ref))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 108:9\<close>
definition
	ord_FMURef :: "FMURef \<Rightarrow> FMURef \<Rightarrow> bool"
where
	"ord_FMURef a   b \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `ord_FMURef` specification.\<close>
		(inv_FMURef a  \<and>  inv_FMURef b)  \<and> 
		\<comment>\<open>User defined body of ord_FMURef.\<close>
		((ref\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f a) < (ref\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f b))"

		 
lemmas inv_FMURef_defs = inv_FMURef_def inv_Name_def inv_Ref_def inv_VDMChar_def inv_VDMNat_def inv_VDMSeq1'_def inv_VDMSeq1'_defs 


	
	
\<comment>\<open>VDM source: FMIValue = compose FMIValue of fmiValue:ValueType, time:Time end
	eq mk_FMIValue(val1, t1) = mk_FMIValue(val2, t2) == ((val1 = val2) and (t1 = t2))
	ord mk_FMIValue(-, t1) < mk_FMIValue(-, t2) == (t1 < t2)\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 114:5\<close>
record FMIValue = 
	fmiValue\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e :: "ValueType"
		 
		 time\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e :: "Time"
	

\<comment>\<open>VDM source: inv_FMIValue: (FMIValue +> bool)
	inv_FMIValue(dummy0) ==
null\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 114:5\<close>
definition
	inv_FMIValue :: "FMIValue \<Rightarrow> bool"
where
	"inv_FMIValue dummy0 \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `inv_FMIValue` specification.\<close>
		( (((inv_ValueType (fmiValue\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e dummy0))) \<and> 
		 (inv_Time (time\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e dummy0)) ))"
 

\<comment>\<open>VDM source: eq_FMIValue: (FMIValue * FMIValue +> bool)
	eq_FMIValue(mk_FMIValue(val1, t1), mk_FMIValue(val2, t2)) ==
((val1 = val2) and (t1 = t2))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 117:8\<close>
definition
	eq_FMIValue :: "FMIValue \<Rightarrow> FMIValue \<Rightarrow> bool"
where
	"eq_FMIValue dummy0   dummy0 \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `eq_FMIValue` specification.\<close>
		(inv_FMIValue dummy0  \<and>  inv_FMIValue dummy0)  \<and> 
		\<comment>\<open>Implicit pattern context conversion\<close>
		(let val1 = (fmiValue\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e dummy0); t1 = (time\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e dummy0); 
			val1 = (fmiValue\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e dummy0); t1 = (time\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e dummy0) in 
		\<comment>\<open>User defined body of eq_FMIValue.\<close>
		(
		\<comment>\<open>Implicit union type parameters projection\<close>
		()))"
 

\<comment>\<open>VDM source: ord_FMIValue: (FMIValue * FMIValue +> bool)
	ord_FMIValue(mk_FMIValue(-, t1), mk_FMIValue(-, t2)) ==
(t1 < t2)\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 120:9\<close>
definition
	ord_FMIValue :: "FMIValue \<Rightarrow> FMIValue \<Rightarrow> bool"
where
	"ord_FMIValue dummy0   dummy0 \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `ord_FMIValue` specification.\<close>
		(inv_FMIValue dummy0  \<and>  inv_FMIValue dummy0)  \<and> 
		\<comment>\<open>Implicit pattern context conversion\<close>
		(let dummy0_ignore = (fmiValue\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e dummy0); t1 = (time\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e dummy0); 
			dummy0_ignore = (fmiValue\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e dummy0); t1 = (time\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e dummy0) in 
		\<comment>\<open>User defined body of ord_FMIValue.\<close>
		\<comment>\<open>Transform a VDM `<` expression into an `ord_Time` call\<close>
	(ord_Time t1   t2))"
 
lemmas inv_FMIValue_defs = inv_FMIValue_def inv_Real1_def inv_Time_def inv_VDMNat_def inv_VDMReal_def inv_ValueType_def inv_bool_def 


	
	
\<comment>\<open>VDM source: Environment = map (Ref) to (FMIValue)\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 126:5\<close>
type_synonym Environment = "(Ref \<rightharpoonup> FMIValue)"
	

\<comment>\<open>VDM source: inv_Environment: (Environment +> bool)
	inv_Environment(dummy0) ==
null\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 126:5\<close>
definition
	inv_Environment :: "Environment \<Rightarrow> bool"
where
	"inv_Environment dummy0 \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `inv_Environment` specification.\<close>
		(((inv_Map (inv_Ref) inv_FMIValue  dummy0)))"
 
lemmas inv_Environment_defs = inv_Environment_def inv_FMIValue_def inv_Map_defs inv_Real1_def inv_Ref_def inv_Time_def inv_VDMNat_def inv_VDMReal_def inv_ValueType_def inv_bool_def 


	
	
\<comment>\<open>VDM source: Equation = (Environment -> Environment)\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 132:5\<close>
type_synonym Equation = "Environment \<Rightarrow> Environment"
	

\<comment>\<open>VDM source: inv_Equation: (Equation +> bool)
	inv_Equation(dummy0) ==
null\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 132:5\<close>
definition
	inv_Equation :: "Equation \<Rightarrow> bool"
where
	"inv_Equation dummy0 \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `inv_Equation` specification.\<close>
		(((inv_Lambda (inv_Environment) (inv_Environment)dummy0)))"

		 
lemmas inv_Equation_defs = inv_Environment_def inv_Equation_def inv_FMIValue_def inv_Lambda_def inv_Map_defs inv_Real1_def inv_Ref_def inv_Time_def inv_VDMNat_def inv_VDMReal_def inv_ValueType_def inv_bool_def 


	
	
\<comment>\<open>VDM source: Variable = compose Variable of name:Name, ref:Ref, time:Time, causality:Causality, type:PortType, clocks:set of (Ref), dependsOn:set of (Ref), contract:Contract end
	inv mk_Variable(-, -, -, causality, type, clocks, dependsOn, contract) == (((causality = <output>) => (contract = <none>)) and (((causality = <input>) => (contract <> <none>)) and (((causality = <input>) => (dependsOn = {})) and (((type = <continous>) => (clocks = {})) and (((type = <discrete>) and (causality = <input>)) => (clocks = {}))))))
	eq mk_Variable(name1, ref1, -, causality1, -, -, -, -) = mk_Variable(name2, ref2, -, causality2, -, -, -, -) == ((name1 = name2) and ((ref1 = ref2) and (causality1 = causality2)))
	ord mk_Variable(name1, ref1, -, -, -, -, -, -) < mk_Variable(name2, ref2, -, -, -, -, -, -) == ((ref1 < ref2) or ((ref1 = ref2) and ((len name1) < (len name2))))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 138:5\<close>
record Variable = 
	name\<^sub>V\<^sub>a\<^sub>r\<^sub>i\<^sub>a\<^sub>b\<^sub>l\<^sub>e :: "Name"
		 
		 ref\<^sub>V\<^sub>a\<^sub>r\<^sub>i\<^sub>a\<^sub>b\<^sub>l\<^sub>e :: "Ref"
		 
		 time\<^sub>V\<^sub>a\<^sub>r\<^sub>i\<^sub>a\<^sub>b\<^sub>l\<^sub>e :: "Time"
		 
		 causality\<^sub>V\<^sub>a\<^sub>r\<^sub>i\<^sub>a\<^sub>b\<^sub>l\<^sub>e :: "Causality"
		 
		 type\<^sub>V\<^sub>a\<^sub>r\<^sub>i\<^sub>a\<^sub>b\<^sub>l\<^sub>e :: "PortType"
		 
		 clocks\<^sub>V\<^sub>a\<^sub>r\<^sub>i\<^sub>a\<^sub>b\<^sub>l\<^sub>e :: "Ref VDMSet"
		 
		 dependsOn\<^sub>V\<^sub>a\<^sub>r\<^sub>i\<^sub>a\<^sub>b\<^sub>l\<^sub>e :: "Ref VDMSet"
		 
		 contract\<^sub>V\<^sub>a\<^sub>r\<^sub>i\<^sub>a\<^sub>b\<^sub>l\<^sub>e :: "Contract"
	

\<comment>\<open>VDM source: inv_Variable: (Variable +> bool)
	inv_Variable(mk_Variable(-, -, -, causality, type, clocks, dependsOn, contract)) ==
(((causality = <output>) => (contract = <none>)) and (((causality = <input>) => (contract <> <none>)) and (((causality = <input>) => (dependsOn = {})) and (((type = <continous>) => (clocks = {})) and (((type = <discrete>) and (causality = <input>)) => (clocks = {}))))))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 147:9\<close>
definition
	inv_Variable :: "Variable \<Rightarrow> bool"
where
	"inv_Variable dummy0 \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `inv_Variable` specification.\<close>
		( (((inv_Name (name\<^sub>V\<^sub>a\<^sub>r\<^sub>i\<^sub>a\<^sub>b\<^sub>l\<^sub>e dummy0))) \<and> 
		 ((inv_Ref (ref\<^sub>V\<^sub>a\<^sub>r\<^sub>i\<^sub>a\<^sub>b\<^sub>l\<^sub>e dummy0))) \<and> 
		 (inv_Time (time\<^sub>V\<^sub>a\<^sub>r\<^sub>i\<^sub>a\<^sub>b\<^sub>l\<^sub>e dummy0)) \<and> 
		 ((inv_Causality (causality\<^sub>V\<^sub>a\<^sub>r\<^sub>i\<^sub>a\<^sub>b\<^sub>l\<^sub>e dummy0))) \<and> 
		 ((inv_PortType (type\<^sub>V\<^sub>a\<^sub>r\<^sub>i\<^sub>a\<^sub>b\<^sub>l\<^sub>e dummy0))) \<and> 
		 ((inv_VDMSet' (inv_Ref) (clocks\<^sub>V\<^sub>a\<^sub>r\<^sub>i\<^sub>a\<^sub>b\<^sub>l\<^sub>e dummy0))) \<and> 
		 ((inv_VDMSet' (inv_Ref) (dependsOn\<^sub>V\<^sub>a\<^sub>r\<^sub>i\<^sub>a\<^sub>b\<^sub>l\<^sub>e dummy0))) \<and> 
		 ((inv_Contract (contract\<^sub>V\<^sub>a\<^sub>r\<^sub>i\<^sub>a\<^sub>b\<^sub>l\<^sub>e dummy0))) ))  \<and> 
		\<comment>\<open>Implicit pattern context conversion\<close>
		(let dummy0_ignore = (name\<^sub>V\<^sub>a\<^sub>r\<^sub>i\<^sub>a\<^sub>b\<^sub>l\<^sub>e dummy0); dummy0_ignore = (ref\<^sub>V\<^sub>a\<^sub>r\<^sub>i\<^sub>a\<^sub>b\<^sub>l\<^sub>e dummy0); dummy0_ignore = (time\<^sub>V\<^sub>a\<^sub>r\<^sub>i\<^sub>a\<^sub>b\<^sub>l\<^sub>e dummy0); causality = (causality\<^sub>V\<^sub>a\<^sub>r\<^sub>i\<^sub>a\<^sub>b\<^sub>l\<^sub>e dummy0); type = (type\<^sub>V\<^sub>a\<^sub>r\<^sub>i\<^sub>a\<^sub>b\<^sub>l\<^sub>e dummy0); clocks = (clocks\<^sub>V\<^sub>a\<^sub>r\<^sub>i\<^sub>a\<^sub>b\<^sub>l\<^sub>e dummy0); dependsOn = (dependsOn\<^sub>V\<^sub>a\<^sub>r\<^sub>i\<^sub>a\<^sub>b\<^sub>l\<^sub>e dummy0); contract = (contract\<^sub>V\<^sub>a\<^sub>r\<^sub>i\<^sub>a\<^sub>b\<^sub>l\<^sub>e dummy0) in 
		\<comment>\<open>User defined body of inv_Variable.\<close>
		(
		\<comment>\<open>Implicit union type parameters projection\<close>
		((((causality = Causality.U_output ) \<longrightarrow> (contract = Contract.U_none )) \<and> (((causality = Causality.U_input ) \<longrightarrow> (contract \<noteq> Contract.U_none )) \<and> (((causality = Causality.U_input ) \<longrightarrow> (dependsOn = {})) \<and> (((type = PortType.U_continous ) \<longrightarrow> (clocks = {})) \<and> (((type = PortType.U_discrete ) \<and> (causality = Causality.U_input )) \<longrightarrow> (clocks = {})))))))))"
 

\<comment>\<open>VDM source: eq_Variable: (Variable * Variable +> bool)
	eq_Variable(mk_Variable(name1, ref1, -, causality1, -, -, -, -), mk_Variable(name2, ref2, -, causality2, -, -, -, -)) ==
((name1 = name2) and ((ref1 = ref2) and (causality1 = causality2)))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 153:9\<close>
definition
	eq_Variable :: "Variable \<Rightarrow> Variable \<Rightarrow> bool"
where
	"eq_Variable dummy0   dummy0 \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `eq_Variable` specification.\<close>
		(inv_Variable dummy0  \<and>  inv_Variable dummy0)  \<and> 
		\<comment>\<open>Implicit pattern context conversion\<close>
		(let name1 = (name\<^sub>V\<^sub>a\<^sub>r\<^sub>i\<^sub>a\<^sub>b\<^sub>l\<^sub>e dummy0); ref1 = (ref\<^sub>V\<^sub>a\<^sub>r\<^sub>i\<^sub>a\<^sub>b\<^sub>l\<^sub>e dummy0); dummy0_ignore = (time\<^sub>V\<^sub>a\<^sub>r\<^sub>i\<^sub>a\<^sub>b\<^sub>l\<^sub>e dummy0); causality1 = (causality\<^sub>V\<^sub>a\<^sub>r\<^sub>i\<^sub>a\<^sub>b\<^sub>l\<^sub>e dummy0); dummy0_ignore = (type\<^sub>V\<^sub>a\<^sub>r\<^sub>i\<^sub>a\<^sub>b\<^sub>l\<^sub>e dummy0); dummy0_ignore = (clocks\<^sub>V\<^sub>a\<^sub>r\<^sub>i\<^sub>a\<^sub>b\<^sub>l\<^sub>e dummy0); dummy0_ignore = (dependsOn\<^sub>V\<^sub>a\<^sub>r\<^sub>i\<^sub>a\<^sub>b\<^sub>l\<^sub>e dummy0); dummy0_ignore = (contract\<^sub>V\<^sub>a\<^sub>r\<^sub>i\<^sub>a\<^sub>b\<^sub>l\<^sub>e dummy0); 
			name1 = (name\<^sub>V\<^sub>a\<^sub>r\<^sub>i\<^sub>a\<^sub>b\<^sub>l\<^sub>e dummy0); ref1 = (ref\<^sub>V\<^sub>a\<^sub>r\<^sub>i\<^sub>a\<^sub>b\<^sub>l\<^sub>e dummy0); dummy0_ignore = (time\<^sub>V\<^sub>a\<^sub>r\<^sub>i\<^sub>a\<^sub>b\<^sub>l\<^sub>e dummy0); causality1 = (causality\<^sub>V\<^sub>a\<^sub>r\<^sub>i\<^sub>a\<^sub>b\<^sub>l\<^sub>e dummy0); dummy0_ignore = (type\<^sub>V\<^sub>a\<^sub>r\<^sub>i\<^sub>a\<^sub>b\<^sub>l\<^sub>e dummy0); dummy0_ignore = (clocks\<^sub>V\<^sub>a\<^sub>r\<^sub>i\<^sub>a\<^sub>b\<^sub>l\<^sub>e dummy0); dummy0_ignore = (dependsOn\<^sub>V\<^sub>a\<^sub>r\<^sub>i\<^sub>a\<^sub>b\<^sub>l\<^sub>e dummy0); dummy0_ignore = (contract\<^sub>V\<^sub>a\<^sub>r\<^sub>i\<^sub>a\<^sub>b\<^sub>l\<^sub>e dummy0) in 
		\<comment>\<open>User defined body of eq_Variable.\<close>
		(
		\<comment>\<open>Implicit union type parameters projection\<close>
		(((name1 = name2) \<and> ((ref1 = ref2) \<and> (causality1 = causality2))))))"
 

\<comment>\<open>VDM source: ord_Variable: (Variable * Variable +> bool)
	ord_Variable(mk_Variable(name1, ref1, -, -, -, -, -, -), mk_Variable(name2, ref2, -, -, -, -, -, -)) ==
((ref1 < ref2) or ((ref1 = ref2) and ((len name1) < (len name2))))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 156:9\<close>
definition
	ord_Variable :: "Variable \<Rightarrow> Variable \<Rightarrow> bool"
where
	"ord_Variable dummy0   dummy0 \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `ord_Variable` specification.\<close>
		(inv_Variable dummy0  \<and>  inv_Variable dummy0)  \<and> 
		\<comment>\<open>Implicit pattern context conversion\<close>
		(let name1 = (name\<^sub>V\<^sub>a\<^sub>r\<^sub>i\<^sub>a\<^sub>b\<^sub>l\<^sub>e dummy0); ref1 = (ref\<^sub>V\<^sub>a\<^sub>r\<^sub>i\<^sub>a\<^sub>b\<^sub>l\<^sub>e dummy0); dummy0_ignore = (time\<^sub>V\<^sub>a\<^sub>r\<^sub>i\<^sub>a\<^sub>b\<^sub>l\<^sub>e dummy0); dummy0_ignore = (causality\<^sub>V\<^sub>a\<^sub>r\<^sub>i\<^sub>a\<^sub>b\<^sub>l\<^sub>e dummy0); dummy0_ignore = (type\<^sub>V\<^sub>a\<^sub>r\<^sub>i\<^sub>a\<^sub>b\<^sub>l\<^sub>e dummy0); dummy0_ignore = (clocks\<^sub>V\<^sub>a\<^sub>r\<^sub>i\<^sub>a\<^sub>b\<^sub>l\<^sub>e dummy0); dummy0_ignore = (dependsOn\<^sub>V\<^sub>a\<^sub>r\<^sub>i\<^sub>a\<^sub>b\<^sub>l\<^sub>e dummy0); dummy0_ignore = (contract\<^sub>V\<^sub>a\<^sub>r\<^sub>i\<^sub>a\<^sub>b\<^sub>l\<^sub>e dummy0); 
			name1 = (name\<^sub>V\<^sub>a\<^sub>r\<^sub>i\<^sub>a\<^sub>b\<^sub>l\<^sub>e dummy0); ref1 = (ref\<^sub>V\<^sub>a\<^sub>r\<^sub>i\<^sub>a\<^sub>b\<^sub>l\<^sub>e dummy0); dummy0_ignore = (time\<^sub>V\<^sub>a\<^sub>r\<^sub>i\<^sub>a\<^sub>b\<^sub>l\<^sub>e dummy0); dummy0_ignore = (causality\<^sub>V\<^sub>a\<^sub>r\<^sub>i\<^sub>a\<^sub>b\<^sub>l\<^sub>e dummy0); dummy0_ignore = (type\<^sub>V\<^sub>a\<^sub>r\<^sub>i\<^sub>a\<^sub>b\<^sub>l\<^sub>e dummy0); dummy0_ignore = (clocks\<^sub>V\<^sub>a\<^sub>r\<^sub>i\<^sub>a\<^sub>b\<^sub>l\<^sub>e dummy0); dummy0_ignore = (dependsOn\<^sub>V\<^sub>a\<^sub>r\<^sub>i\<^sub>a\<^sub>b\<^sub>l\<^sub>e dummy0); dummy0_ignore = (contract\<^sub>V\<^sub>a\<^sub>r\<^sub>i\<^sub>a\<^sub>b\<^sub>l\<^sub>e dummy0) in 
		\<comment>\<open>User defined body of ord_Variable.\<close>
		((ref1 < ref2) \<or> ((ref1 = ref2) \<and> ((len name1) < (len name2)))))"
 
lemmas inv_Variable_defs = inv_Causality_def inv_Contract_def inv_Name_def inv_PortType_def inv_Real1_def inv_Ref_def inv_Time_def inv_True_def inv_VDMChar_def inv_VDMNat_def inv_VDMReal_def inv_VDMSeq1'_def inv_VDMSeq1'_defs inv_VDMSet'_def inv_VDMSet'_defs inv_Variable_def 


	
	
\<comment>\<open>VDM source: TimeBasedClock = compose TimeBasedClock of name:Name, shift:Real1, period:Real1, interval:Interval, master:FMURef end
	inv clock == ((clock.interval) <> <triggered>)\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 161:5\<close>
record TimeBasedClock = 
	name\<^sub>T\<^sub>i\<^sub>m\<^sub>e\<^sub>B\<^sub>a\<^sub>s\<^sub>e\<^sub>d\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k :: "Name"
		 
		 shift\<^sub>T\<^sub>i\<^sub>m\<^sub>e\<^sub>B\<^sub>a\<^sub>s\<^sub>e\<^sub>d\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k :: "Real1"
		 
		 period\<^sub>T\<^sub>i\<^sub>m\<^sub>e\<^sub>B\<^sub>a\<^sub>s\<^sub>e\<^sub>d\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k :: "Real1"
		 
		 interval\<^sub>T\<^sub>i\<^sub>m\<^sub>e\<^sub>B\<^sub>a\<^sub>s\<^sub>e\<^sub>d\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k :: "Interval"
		 
		 master\<^sub>T\<^sub>i\<^sub>m\<^sub>e\<^sub>B\<^sub>a\<^sub>s\<^sub>e\<^sub>d\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k :: "FMURef"
	

\<comment>\<open>VDM source: inv_TimeBasedClock: (TimeBasedClock +> bool)
	inv_TimeBasedClock(clock) ==
((clock.interval) <> <triggered>)\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 167:9\<close>
definition
	inv_TimeBasedClock :: "TimeBasedClock \<Rightarrow> bool"
where
	"inv_TimeBasedClock clock \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `inv_TimeBasedClock` specification.\<close>
		( (((inv_Name (name\<^sub>T\<^sub>i\<^sub>m\<^sub>e\<^sub>B\<^sub>a\<^sub>s\<^sub>e\<^sub>d\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k clock))) \<and> 
		 ((inv_Real1 (shift\<^sub>T\<^sub>i\<^sub>m\<^sub>e\<^sub>B\<^sub>a\<^sub>s\<^sub>e\<^sub>d\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k clock))) \<and> 
		 ((inv_Real1 (period\<^sub>T\<^sub>i\<^sub>m\<^sub>e\<^sub>B\<^sub>a\<^sub>s\<^sub>e\<^sub>d\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k clock))) \<and> 
		 ((inv_Interval (interval\<^sub>T\<^sub>i\<^sub>m\<^sub>e\<^sub>B\<^sub>a\<^sub>s\<^sub>e\<^sub>d\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k clock))) \<and> 
		 (inv_FMURef (master\<^sub>T\<^sub>i\<^sub>m\<^sub>e\<^sub>B\<^sub>a\<^sub>s\<^sub>e\<^sub>d\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k clock)) ))  \<and> 
		\<comment>\<open>User defined body of inv_TimeBasedClock.\<close>
		((interval\<^sub>T\<^sub>i\<^sub>m\<^sub>e\<^sub>B\<^sub>a\<^sub>s\<^sub>e\<^sub>d\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k clock) \<noteq> Interval.U_triggered )"

		
lemmas inv_TimeBasedClock_defs = inv_FMURef_def inv_Interval_def inv_Name_def inv_Real1_def inv_Ref_def inv_TimeBasedClock_def inv_True_def inv_VDMChar_def inv_VDMNat_def inv_VDMReal_def inv_VDMSeq1'_def inv_VDMSeq1'_defs 


	
	
\<comment>\<open>VDM source: Clock = compose Clock of name:Name, ref:Ref, type:Causality, interval:Interval, dependsOn:set of (Ref), equations:set of (Ref) end
	inv clock == ((((clock.type) = <output>) => ((clock.interval) = <triggered>)) and (((clock.type) = <input>) => ((clock.dependsOn) = {})))
	eq mk_Clock(name1, ref1, type1, interval1, -, -) = mk_Clock(name2, ref2, type2, interval2, -, -) == ((name1 = name2) and ((ref1 = ref2) and ((type1 = type2) and (interval1 = interval2))))
	ord c1 < c2 == ((c1.ref) < (c2.ref))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 173:5\<close>
record Clock = 
	name\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k :: "Name"
		 
		 ref\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k :: "Ref"
		 
		 type\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k :: "Causality"
		 
		 interval\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k :: "Interval"
		 
		 dependsOn\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k :: "Ref VDMSet"
		 
		 equations\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k :: "Ref VDMSet"
	

\<comment>\<open>VDM source: inv_Clock: (Clock +> bool)
	inv_Clock(clock) ==
((((clock.type) = <output>) => ((clock.interval) = <triggered>)) and (((clock.type) = <input>) => ((clock.dependsOn) = {})))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 180:9\<close>
definition
	inv_Clock :: "Clock \<Rightarrow> bool"
where
	"inv_Clock clock \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `inv_Clock` specification.\<close>
		( (((inv_Name (name\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k clock))) \<and> 
		 ((inv_Ref (ref\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k clock))) \<and> 
		 ((inv_Causality (type\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k clock))) \<and> 
		 ((inv_Interval (interval\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k clock))) \<and> 
		 ((inv_VDMSet' (inv_Ref) (dependsOn\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k clock))) \<and> 
		 ((inv_VDMSet' (inv_Ref) (equations\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k clock))) ))  \<and> 
		\<comment>\<open>User defined body of inv_Clock.\<close>
		((((type\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k clock) = Causality.U_output ) \<longrightarrow> ((interval\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k clock) = Interval.U_triggered )) \<and> (((type\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k clock) = Causality.U_input ) \<longrightarrow> ((dependsOn\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k clock) = {})))"

		

\<comment>\<open>VDM source: eq_Clock: (Clock * Clock +> bool)
	eq_Clock(mk_Clock(name1, ref1, type1, interval1, -, -), mk_Clock(name2, ref2, type2, interval2, -, -)) ==
((name1 = name2) and ((ref1 = ref2) and ((type1 = type2) and (interval1 = interval2))))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 183:8\<close>
definition
	eq_Clock :: "Clock \<Rightarrow> Clock \<Rightarrow> bool"
where
	"eq_Clock dummy0   dummy0 \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `eq_Clock` specification.\<close>
		(inv_Clock dummy0  \<and>  inv_Clock dummy0)  \<and> 
		\<comment>\<open>Implicit pattern context conversion\<close>
		(let name1 = (name\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k dummy0); ref1 = (ref\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k dummy0); type1 = (type\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k dummy0); interval1 = (interval\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k dummy0); dummy0_ignore = (dependsOn\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k dummy0); dummy0_ignore = (equations\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k dummy0); 
			name1 = (name\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k dummy0); ref1 = (ref\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k dummy0); type1 = (type\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k dummy0); interval1 = (interval\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k dummy0); dummy0_ignore = (dependsOn\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k dummy0); dummy0_ignore = (equations\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k dummy0) in 
		\<comment>\<open>User defined body of eq_Clock.\<close>
		(
		\<comment>\<open>Implicit union type parameters projection\<close>
		(((name1 = name2) \<and> ((ref1 = ref2) \<and> ((type1 = type2) \<and> (interval1 = interval2)))))))"

		

\<comment>\<open>VDM source: ord_Clock: (Clock * Clock +> bool)
	ord_Clock(c1, c2) ==
((c1.ref) < (c2.ref))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 185:9\<close>
definition
	ord_Clock :: "Clock \<Rightarrow> Clock \<Rightarrow> bool"
where
	"ord_Clock c1   c2 \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `ord_Clock` specification.\<close>
		(inv_Clock c1  \<and>  inv_Clock c2)  \<and> 
		\<comment>\<open>User defined body of ord_Clock.\<close>
		((ref\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k c1) < (ref\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k c2))"

		
lemmas inv_Clock_defs = inv_Causality_def inv_Clock_def inv_Interval_def inv_Name_def inv_Ref_def inv_True_def inv_VDMChar_def inv_VDMNat_def inv_VDMSeq1'_def inv_VDMSeq1'_defs inv_VDMSet'_def inv_VDMSet'_defs 


	
	
\<comment>\<open>VDM source: clock_refs: (set of (Clock) -> set of (Ref))
	clock_refs(cs) ==
{(c.ref) | c in set cs}
	pre true
	post ((card cs) = (card RESULT))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 190:5\<close>

\<comment>\<open>VDM source: pre_clock_refs: (set of (Clock) +> bool)
	pre_clock_refs(cs) ==
true\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 193:9\<close>
definition
	pre_clock_refs :: "Clock VDMSet \<Rightarrow> bool"
where
	"pre_clock_refs cs \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `pre_clock_refs` specification.\<close>
		((inv_VDMSet' inv_Clock  cs))  \<and> 
		\<comment>\<open>User defined body of pre_clock_refs.\<close>
		(True::\<bool>)"


\<comment>\<open>VDM source: post_clock_refs: (set of (Clock) * set of (Ref) +> bool)
	post_clock_refs(cs, RESULT) ==
((card cs) = (card RESULT))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 195:17\<close>
definition
	post_clock_refs :: "Clock VDMSet \<Rightarrow> Ref VDMSet \<Rightarrow> bool"
where
	"post_clock_refs cs   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `post_clock_refs` specification.\<close>
		((inv_VDMSet' inv_Clock  cs)  \<and>  (inv_VDMSet' (inv_Ref) RESULT))  \<and> 
		\<comment>\<open>User defined body of post_clock_refs.\<close>
		((vdm_card cs) = (vdm_card RESULT))"

definition
	clock_refs :: "Clock VDMSet \<Rightarrow> Ref VDMSet"
where
	"clock_refs cs \<equiv> 
	\<comment>\<open>User defined body of clock_refs.\<close>
	{ (ref\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k c) | c .  ((c \<in>cs))  }"

	
	
\<comment>\<open>VDM source: var_refs: (set1 of (Variable) -> set1 of (Ref))
	var_refs(vs) ==
{(v.ref) | v in set vs}
	pre true
	post ((card vs) = (card RESULT))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 198:5\<close>

\<comment>\<open>VDM source: pre_var_refs: (set1 of (Variable) +> bool)
	pre_var_refs(vs) ==
true\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 201:9\<close>
definition
	pre_var_refs :: "Variable VDMSet1 \<Rightarrow> bool"
where
	"pre_var_refs vs \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `pre_var_refs` specification.\<close>
		((inv_VDMSet1' inv_Variable  vs))  \<and> 
		\<comment>\<open>User defined body of pre_var_refs.\<close>
		(True::\<bool>)"


\<comment>\<open>VDM source: post_var_refs: (set1 of (Variable) * set1 of (Ref) +> bool)
	post_var_refs(vs, RESULT) ==
((card vs) = (card RESULT))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 203:17\<close>
definition
	post_var_refs :: "Variable VDMSet1 \<Rightarrow> Ref VDMSet1 \<Rightarrow> bool"
where
	"post_var_refs vs   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `post_var_refs` specification.\<close>
		((inv_VDMSet1' inv_Variable  vs)  \<and>  (inv_VDMSet1' (inv_Ref) RESULT))  \<and> 
		\<comment>\<open>User defined body of post_var_refs.\<close>
		((vdm_card vs) = (vdm_card RESULT))"

definition
	var_refs :: "Variable VDMSet1 \<Rightarrow> Ref VDMSet1"
where
	"var_refs vs \<equiv> 
	\<comment>\<open>User defined body of var_refs.\<close>
	{ (ref\<^sub>V\<^sub>a\<^sub>r\<^sub>i\<^sub>a\<^sub>b\<^sub>l\<^sub>e v) | v .  ((v \<in>vs))  }"

	
	
\<comment>\<open>VDM source: fold[T]: ((@T * @T -> @T) * @T * seq of (@T) +> @T)
	fold(f, e, s) ==
(if (s = [])
then e
else (if ((len s) = 1)
then (hd s)
else let lens:nat1 = (len s) in f((fold)[@T](f, e, (s(1, ... ,(lens div 2)))), (fold)[@T](f, e, (s(((lens div 2) + 1), ... ,lens))))))
	measure (len s)\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 208:3\<close>

\<comment>\<open>VDM source: pre_fold[T]: ((@T * @T -> @T) * @T * seq of (@T) +> bool)
	pre_fold(f, e, s) ==
null\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 208:3\<close>
definition
	pre_fold :: "('T \<Rightarrow> bool) \<Rightarrow> ('T \<Rightarrow> 'T \<Rightarrow> 'T) \<Rightarrow> 'T \<Rightarrow> 'T VDMSeq \<Rightarrow> bool"
where
	"pre_fold inv_T   f   e   s \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `pre_fold` specification.\<close>
		((inv_Lambda inv_T (inv_Lambda inv_T inv_T)f)  \<and>  inv_T e  \<and>  (inv_VDMSeq' inv_T s))"


\<comment>\<open>VDM source: post_fold[T]: ((@T * @T -> @T) * @T * seq of (@T) * @T +> bool)
	post_fold(f, e, s, RESULT) ==
null\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 208:3\<close>
definition
	post_fold :: "('T \<Rightarrow> bool) \<Rightarrow> ('T \<Rightarrow> 'T \<Rightarrow> 'T) \<Rightarrow> 'T \<Rightarrow> 'T VDMSeq \<Rightarrow> 'T \<Rightarrow> bool"
where
	"post_fold inv_T   f   e   s   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_fold` specification.\<close>
		((inv_Lambda inv_T (inv_Lambda inv_T inv_T)f)  \<and>  inv_T e  \<and>  (inv_VDMSeq' inv_T s)  \<and>  inv_T RESULT)"

fun
	fold :: "('T \<Rightarrow> bool) \<Rightarrow> ('T \<Rightarrow> 'T \<Rightarrow> 'T) \<Rightarrow> 'T \<Rightarrow> 'T VDMSeq \<Rightarrow> 'T"
where
	"fold inv_T   f   e   s = 
	\<comment>\<open>User defined body of fold.\<close>
	\<comment>\<open>Implicit check on generic type invariant for `fold`.\<close>
	(if post_fold inv_T   f   e   s ((
		if ((s = [])) then
		(e)
		else
		((
		if (((len s) = (1::VDMNat1))) then
		((hd s))
		else
		((
		let 
(lens::VDMNat1) = (len s)
		in
			(if ((inv_VDMNat1 lens)) then
			(f (fold inv_T   f   e   (s {(1::VDMNat1)$$(lens vdmdiv (2::VDMNat1))}))   (fold inv_T   f   e   (s {((lens vdmdiv (2::VDMNat1)) + (1::VDMNat1))$$lens})))
		 else
			undefined
		)
		)))))) then
			(
		if ((s = [])) then
		(e)
		else
		((
		if (((len s) = (1::VDMNat1))) then
		((hd s))
		else
		((
		let 
(lens::VDMNat1) = (len s)
		in
			(if ((inv_VDMNat1 lens)) then
			(f (fold inv_T   f   e   (s {(1::VDMNat1)$$(lens vdmdiv (2::VDMNat1))}))   (fold inv_T   f   e   (s {((lens vdmdiv (2::VDMNat1)) + (1::VDMNat1))$$lens})))
		 else
			undefined
		)
		)))))
		 else
			undefined
		)
		"

	
	
\<comment>\<open>VDM source: fold1[T]: ((@T * @T -> @T) * seq1 of (@T) +> @T)
	fold1(f, s) ==
(if ((len s) = 1)
then (hd s)
else let lens:nat1 = (len s) in f((fold1)[@T](f, (s(1, ... ,(lens div 2)))), (fold1)[@T](f, (s(((lens div 2) + 1), ... ,lens)))))
	pre true
	measure (len s)\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 225:3\<close>

\<comment>\<open>VDM source: pre_fold1[T]: ((@T * @T -> @T) * seq1 of (@T) +> bool)
	pre_fold1(f, s) ==
true\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 234:5\<close>
definition
	pre_fold1 :: "('T \<Rightarrow> bool) \<Rightarrow> ('T \<Rightarrow> 'T \<Rightarrow> 'T) \<Rightarrow> 'T VDMSeq1 \<Rightarrow> bool"
where
	"pre_fold1 inv_T   f   s \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `pre_fold1` specification.\<close>
		((inv_Lambda inv_T (inv_Lambda inv_T inv_T)f)  \<and>  (inv_VDMSeq1' inv_T s))  \<and> 
		\<comment>\<open>User defined body of pre_fold1.\<close>
		\<comment>\<open>Implicit check on generic type invariant for `pre_fold1`.\<close>
		(if post_pre_fold1 inv_T   f   s ((True::\<bool>)) then	(True::\<bool>) else	undefined)"


\<comment>\<open>VDM source: post_fold1[T]: ((@T * @T -> @T) * seq1 of (@T) * @T +> bool)
	post_fold1(f, s, RESULT) ==
null\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 225:3\<close>
definition
	post_fold1 :: "('T \<Rightarrow> bool) \<Rightarrow> ('T \<Rightarrow> 'T \<Rightarrow> 'T) \<Rightarrow> 'T VDMSeq1 \<Rightarrow> 'T \<Rightarrow> bool"
where
	"post_fold1 inv_T   f   s   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_fold1` specification.\<close>
		((inv_Lambda inv_T (inv_Lambda inv_T inv_T)f)  \<and>  (inv_VDMSeq1' inv_T s)  \<and>  inv_T RESULT)"

fun
	fold1 :: "('T \<Rightarrow> bool) \<Rightarrow> ('T \<Rightarrow> 'T \<Rightarrow> 'T) \<Rightarrow> 'T VDMSeq1 \<Rightarrow> 'T"
where
	"fold1 inv_T   f   s = 
	\<comment>\<open>User defined body of fold1.\<close>
	\<comment>\<open>Implicit check on generic type invariant for `fold1`.\<close>
	(if post_fold1 inv_T   f   s ((
		if (((len s) = (1::VDMNat1))) then
		((hd s))
		else
		((
		let 
(lens::VDMNat1) = (len s)
		in
			(if ((inv_VDMNat1 lens)) then
			(f (fold1 inv_T   f   (s {(1::VDMNat1)$$(lens vdmdiv (2::VDMNat1))}))   (fold1 inv_T   f   (s {((lens vdmdiv (2::VDMNat1)) + (1::VDMNat1))$$lens})))
		 else
			undefined
		)
		)))) then
			(
		if (((len s) = (1::VDMNat1))) then
		((hd s))
		else
		((
		let 
(lens::VDMNat1) = (len s)
		in
			(if ((inv_VDMNat1 lens)) then
			(f (fold1 inv_T   f   (s {(1::VDMNat1)$$(lens vdmdiv (2::VDMNat1))}))   (fold1 inv_T   f   (s {((lens vdmdiv (2::VDMNat1)) + (1::VDMNat1))$$lens})))
		 else
			undefined
		)
		)))
		 else
			undefined
		)
		"

	
	
\<comment>\<open>VDM source: maxxs[T]: (seq1 of (@T) * (@T * @T -> @T) -> @T)
	maxxs(s, lt_ord) ==
(fold1)[@T](lt_ord, s)
	pre (pre_fold1)[@T](lt_ord, s)
	post ((RESULT in set (elems s)) and (forall e in set (elems s) & ((lt_ord(RESULT, e) = RESULT) or (RESULT = e))))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 238:5\<close>

\<comment>\<open>VDM source: pre_maxxs[T]: (seq1 of (@T) * (@T * @T -> @T) +> bool)
	pre_maxxs(s, lt_ord) ==
(pre_fold1)[@T](lt_ord, s)\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 241:9\<close>
definition
	pre_maxxs :: "('T \<Rightarrow> bool) \<Rightarrow> 'T VDMSeq1 \<Rightarrow> ('T \<Rightarrow> 'T \<Rightarrow> 'T) \<Rightarrow> bool"
where
	"pre_maxxs inv_T   s   lt_ord \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `pre_maxxs` specification.\<close>
		((inv_VDMSeq1' inv_T s)  \<and>  (inv_Lambda inv_T (inv_Lambda inv_T inv_T)lt_ord))  \<and> 
		\<comment>\<open>User defined body of pre_maxxs.\<close>
		\<comment>\<open>Implicit check on generic type invariant for `pre_maxxs`.\<close>
		(if post_pre_maxxs inv_T   s   lt_ord ((pre_fold1 inv_T   lt_ord   s)) then	(pre_fold1 inv_T   lt_ord   s) else	undefined)"


\<comment>\<open>VDM source: post_maxxs[T]: (seq1 of (@T) * (@T * @T -> @T) * @T +> bool)
	post_maxxs(s, lt_ord, RESULT) ==
((RESULT in set (elems s)) and (forall e in set (elems s) & ((lt_ord(RESULT, e) = RESULT) or (RESULT = e))))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 243:31\<close>
definition
	post_maxxs :: "('T \<Rightarrow> bool) \<Rightarrow> 'T VDMSeq1 \<Rightarrow> ('T \<Rightarrow> 'T \<Rightarrow> 'T) \<Rightarrow> 'T \<Rightarrow> bool"
where
	"post_maxxs inv_T   s   lt_ord   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `post_maxxs` specification.\<close>
		((inv_VDMSeq1' inv_T s)  \<and>  (inv_Lambda inv_T (inv_Lambda inv_T inv_T)lt_ord)  \<and>  inv_T RESULT)  \<and> 
		\<comment>\<open>User defined body of post_maxxs.\<close>
		\<comment>\<open>Implicit check on generic type invariant for `post_maxxs`.\<close>
		(if post_post_maxxs inv_T   s   lt_ord   RESULT (((RESULT \<in> (elems s)) \<and> (\<forall> e \<in> (elems s)  . (((lt_ord RESULT   e) = RESULT) \<or> (RESULT = e))))) then	((RESULT \<in> (elems s)) \<and> (\<forall> e \<in> (elems s)  . (((lt_ord RESULT   e) = RESULT) \<or> (RESULT = e)))) else	undefined)"

definition
	maxxs :: "('T \<Rightarrow> bool) \<Rightarrow> 'T VDMSeq1 \<Rightarrow> ('T \<Rightarrow> 'T \<Rightarrow> 'T) \<Rightarrow> 'T"
where
	"maxxs inv_T   s   lt_ord \<equiv> 
	\<comment>\<open>User defined body of maxxs.\<close>
	\<comment>\<open>Implicit check on generic type invariant for `maxxs`.\<close>
	(if post_maxxs inv_T   s   lt_ord ((fold1 inv_T   lt_ord   s)) then	(fold1 inv_T   lt_ord   s) else	undefined)"

	
	
\<comment>\<open>VDM source: IOLeo = compose IOLeo of LFinput:set of (Variable), LFoutput:set of (Variable) end
	inv mk_IOLeo(LFinput, LFoutput) == ((LFinput union LFoutput) <> {})\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 247:5\<close>
record IOLeo = 
	LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o :: "Variable VDMSet"
		 
		 LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o :: "Variable VDMSet"
	

\<comment>\<open>VDM source: inv_IOLeo: (IOLeo +> bool)
	inv_IOLeo(mk_IOLeo(LFinput, LFoutput)) ==
((LFinput union LFoutput) <> {})\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 251:9\<close>
definition
	inv_IOLeo :: "IOLeo \<Rightarrow> bool"
where
	"inv_IOLeo dummy0 \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `inv_IOLeo` specification.\<close>
		( (((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o dummy0))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o dummy0))) ))  \<and> 
		\<comment>\<open>Implicit pattern context conversion\<close>
		(let LFinput = (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o dummy0); LFoutput = (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o dummy0) in 
		\<comment>\<open>User defined body of inv_IOLeo.\<close>
		((LFinput \<union> LFoutput) \<noteq> {}))"

		
lemmas inv_IOLeo_defs = inv_Causality_def inv_Contract_def inv_IOLeo_def inv_Name_def inv_PortType_def inv_Real1_def inv_Ref_def inv_Time_def inv_True_def inv_VDMChar_def inv_VDMNat_def inv_VDMReal_def inv_VDMSeq1'_def inv_VDMSeq1'_defs inv_VDMSet'_def inv_VDMSet'_defs inv_Variable_def 


	
	
\<comment>\<open>VDM source: FMU = compose FMU of id:nat, name:Name, clocks:set of (Clock), io:IOLeo, mode:FMUMode, time:Time, stepped:bool, maxStep:Real1, env:Environment, activeClocks:set of (Ref), activeEquations:set of (Equation) end
	inv mk_FMU(-, -, clocks, io, mode, time, -, -, env, activeClocks, activeEquations) == let vars:set1 of (Variable) = ((io.LFinput) union (io.LFoutput)) in (pre_var_refs(vars) and (pre_clock_refs(clocks) and let crefs:set of (Ref) = clock_refs(clocks), vrefs:set1 of (Ref) = var_refs(vars), refs:set1 of (Ref) = (crefs union vrefs) in (post_clock_refs(clocks, crefs) and (post_var_refs(vars, vrefs) and (((crefs inter vrefs) = {}) and (((card refs) = ((card clocks) + (card vars))) and (((dom env) subset refs) and ((activeClocks subset crefs) and (((mode <> <EVENT>) => ((activeClocks = {}) and ((activeEquations = {}) and ((time.i) = 0)))) and (((mode <> <EVENT>) => (activeEquations = {})) and (((mode <> <EVENT>) => ((time.i) = 0)) and (forall var in set vars & ((var.clocks) subset crefs)))))))))))))
	eq fmu1 = fmu2 == ((fmu1.id) = (fmu2.id))
	ord fmu1 < fmu2 == ((fmu1.id) < (fmu2.id))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 254:5\<close>
record FMU = 
	id\<^sub>F\<^sub>M\<^sub>U :: "VDMNat"
		 
		 name\<^sub>F\<^sub>M\<^sub>U :: "Name"
		 
		 clocks\<^sub>F\<^sub>M\<^sub>U :: "Clock VDMSet"
		 
		 io\<^sub>F\<^sub>M\<^sub>U :: "IOLeo"
		 
		 mode\<^sub>F\<^sub>M\<^sub>U :: "FMUMode"
		 
		 time\<^sub>F\<^sub>M\<^sub>U :: "Time"
		 
		 stepped\<^sub>F\<^sub>M\<^sub>U :: "bool"
		 
		 maxStep\<^sub>F\<^sub>M\<^sub>U :: "Real1"
		 
		 env\<^sub>F\<^sub>M\<^sub>U :: "Environment"
		 
		 activeClocks\<^sub>F\<^sub>M\<^sub>U :: "Ref VDMSet"
		 
		 activeEquations\<^sub>F\<^sub>M\<^sub>U :: "Equation VDMSet"
	

\<comment>\<open>VDM source: inv_FMU: (FMU +> bool)
	inv_FMU(mk_FMU(-, -, clocks, io, mode, time, -, -, env, activeClocks, activeEquations)) ==
let vars:set1 of (Variable) = ((io.LFinput) union (io.LFoutput)) in (pre_var_refs(vars) and (pre_clock_refs(clocks) and let crefs:set of (Ref) = clock_refs(clocks), vrefs:set1 of (Ref) = var_refs(vars), refs:set1 of (Ref) = (crefs union vrefs) in (post_clock_refs(clocks, crefs) and (post_var_refs(vars, vrefs) and (((crefs inter vrefs) = {}) and (((card refs) = ((card clocks) + (card vars))) and (((dom env) subset refs) and ((activeClocks subset crefs) and (((mode <> <EVENT>) => ((activeClocks = {}) and ((activeEquations = {}) and ((time.i) = 0)))) and (((mode <> <EVENT>) => (activeEquations = {})) and (((mode <> <EVENT>) => ((time.i) = 0)) and (forall var in set vars & ((var.clocks) subset crefs)))))))))))))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 267:9\<close>
definition
	inv_FMU :: "FMU \<Rightarrow> bool"
where
	"inv_FMU dummy0 \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `inv_FMU` specification.\<close>
		( (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U dummy0))) \<and> 
		 ((inv_Name (name\<^sub>F\<^sub>M\<^sub>U dummy0))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U dummy0))) \<and> 
		 (inv_IOLeo (io\<^sub>F\<^sub>M\<^sub>U dummy0)) \<and> 
		 ((inv_FMUMode (mode\<^sub>F\<^sub>M\<^sub>U dummy0))) \<and> 
		 (inv_Time (time\<^sub>F\<^sub>M\<^sub>U dummy0)) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U dummy0))) \<and> 
		 ((inv_Real1 (maxStep\<^sub>F\<^sub>M\<^sub>U dummy0))) \<and> 
		 ((inv_Environment (env\<^sub>F\<^sub>M\<^sub>U dummy0))) \<and> 
		 ((inv_VDMSet' (inv_Ref) (activeClocks\<^sub>F\<^sub>M\<^sub>U dummy0))) \<and> 
		 ((inv_VDMSet' (inv_Equation) (activeEquations\<^sub>F\<^sub>M\<^sub>U dummy0))) ))  \<and> 
		\<comment>\<open>Implicit pattern context conversion\<close>
		(let dummy0_ignore = (id\<^sub>F\<^sub>M\<^sub>U dummy0); dummy0_ignore = (name\<^sub>F\<^sub>M\<^sub>U dummy0); clocks = (clocks\<^sub>F\<^sub>M\<^sub>U dummy0); io = (io\<^sub>F\<^sub>M\<^sub>U dummy0); mode = (mode\<^sub>F\<^sub>M\<^sub>U dummy0); time = (time\<^sub>F\<^sub>M\<^sub>U dummy0); dummy0_ignore = (stepped\<^sub>F\<^sub>M\<^sub>U dummy0); dummy0_ignore = (maxStep\<^sub>F\<^sub>M\<^sub>U dummy0); env = (env\<^sub>F\<^sub>M\<^sub>U dummy0); activeClocks = (activeClocks\<^sub>F\<^sub>M\<^sub>U dummy0); activeEquations = (activeEquations\<^sub>F\<^sub>M\<^sub>U dummy0) in 
		\<comment>\<open>User defined body of inv_FMU.\<close>
		(
		\<comment>\<open>Implicit union type parameters projection\<close>
		()))"
 

\<comment>\<open>VDM source: eq_FMU: (FMU * FMU +> bool)
	eq_FMU(fmu1, fmu2) ==
((fmu1.id) = (fmu2.id))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 302:12\<close>
definition
	eq_FMU :: "FMU \<Rightarrow> FMU \<Rightarrow> bool"
where
	"eq_FMU fmu1   fmu2 \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `eq_FMU` specification.\<close>
		(inv_FMU fmu1  \<and>  inv_FMU fmu2)  \<and> 
		\<comment>\<open>User defined body of eq_FMU.\<close>
		((id\<^sub>F\<^sub>M\<^sub>U fmu1) = (id\<^sub>F\<^sub>M\<^sub>U fmu2))"
 

\<comment>\<open>VDM source: ord_FMU: (FMU * FMU +> bool)
	ord_FMU(fmu1, fmu2) ==
((fmu1.id) < (fmu2.id))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 304:13\<close>
definition
	ord_FMU :: "FMU \<Rightarrow> FMU \<Rightarrow> bool"
where
	"ord_FMU fmu1   fmu2 \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `ord_FMU` specification.\<close>
		(inv_FMU fmu1  \<and>  inv_FMU fmu2)  \<and> 
		\<comment>\<open>User defined body of ord_FMU.\<close>
		((id\<^sub>F\<^sub>M\<^sub>U fmu1) < (id\<^sub>F\<^sub>M\<^sub>U fmu2))"
 
lemmas inv_FMU_defs = inv_Causality_def inv_Clock_def inv_Contract_def inv_Environment_def inv_Equation_def inv_FMIValue_def inv_FMU_def inv_FMUMode_def inv_IOLeo_def inv_Interval_def inv_Lambda_def inv_Map_defs inv_Name_def inv_PortType_def inv_Real1_def inv_Ref_def inv_Time_def inv_True_def inv_VDMChar_def inv_VDMNat_def inv_VDMReal_def inv_VDMSeq1'_def inv_VDMSeq1'_defs inv_VDMSet'_def inv_VDMSet'_defs inv_ValueType_def inv_Variable_def inv_bool_def 


	
	
\<comment>\<open>VDM source: derefClock: (FMU * Ref -> Clock)
	derefClock(fmu, ref) ==
(iota c in set (fmu.clocks) & ((c.ref) = ref))
	pre (exists [c in set (fmu.clocks)] & ((c.ref) = ref))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 311:5\<close>

\<comment>\<open>VDM source: pre_derefClock: (FMU * Ref +> bool)
	pre_derefClock(fmu, ref) ==
(exists [c in set (fmu.clocks)] & ((c.ref) = ref))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 314:9\<close>
definition
	pre_derefClock :: "FMU \<Rightarrow> Ref \<Rightarrow> bool"
where
	"pre_derefClock fmu   ref \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `pre_derefClock` specification.\<close>
		(inv_FMU fmu  \<and>  (inv_Ref ref))  \<and> 
		\<comment>\<open>User defined body of pre_derefClock.\<close>
		(\<exists> c \<in> (clocks\<^sub>F\<^sub>M\<^sub>U fmu)  . ((ref\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k c) = ref))"


\<comment>\<open>VDM source: post_derefClock: (FMU * Ref * Clock +> bool)
	post_derefClock(fmu, ref, RESULT) ==
null\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 311:5\<close>
definition
	post_derefClock :: "FMU \<Rightarrow> Ref \<Rightarrow> Clock \<Rightarrow> bool"
where
	"post_derefClock fmu   ref   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_derefClock` specification.\<close>
		(inv_FMU fmu  \<and>  (inv_Ref ref)  \<and>  inv_Clock RESULT)"

definition
	derefClock :: "FMU \<Rightarrow> Ref \<Rightarrow> Clock"
where
	"derefClock fmu   ref \<equiv> 
	\<comment>\<open>User defined body of derefClock.\<close>
	(THE c. (((c \<in>(clocks\<^sub>F\<^sub>M\<^sub>U fmu))) \<and> ((ref\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k c) = ref)))"

	
	
\<comment>\<open>VDM source: derefInput: (FMU * Ref -> Variable)
	derefInput(fmu, ref) ==
(iota c in set ((fmu.io).LFinput) & ((c.ref) = ref))
	pre (exists [c in set ((fmu.io).LFinput)] & ((c.ref) = ref))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 319:5\<close>

\<comment>\<open>VDM source: pre_derefInput: (FMU * Ref +> bool)
	pre_derefInput(fmu, ref) ==
(exists [c in set ((fmu.io).LFinput)] & ((c.ref) = ref))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 322:9\<close>
definition
	pre_derefInput :: "FMU \<Rightarrow> Ref \<Rightarrow> bool"
where
	"pre_derefInput fmu   ref \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `pre_derefInput` specification.\<close>
		(inv_FMU fmu  \<and>  (inv_Ref ref))  \<and> 
		\<comment>\<open>User defined body of pre_derefInput.\<close>
		(\<exists> c \<in> (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U fmu))  . ((ref\<^sub>V\<^sub>a\<^sub>r\<^sub>i\<^sub>a\<^sub>b\<^sub>l\<^sub>e c) = ref))"


\<comment>\<open>VDM source: post_derefInput: (FMU * Ref * Variable +> bool)
	post_derefInput(fmu, ref, RESULT) ==
null\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 319:5\<close>
definition
	post_derefInput :: "FMU \<Rightarrow> Ref \<Rightarrow> Variable \<Rightarrow> bool"
where
	"post_derefInput fmu   ref   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_derefInput` specification.\<close>
		(inv_FMU fmu  \<and>  (inv_Ref ref)  \<and>  inv_Variable RESULT)"

definition
	derefInput :: "FMU \<Rightarrow> Ref \<Rightarrow> Variable"
where
	"derefInput fmu   ref \<equiv> 
	\<comment>\<open>User defined body of derefInput.\<close>
	(THE c. (((c \<in>(LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U fmu)))) \<and> ((ref\<^sub>V\<^sub>a\<^sub>r\<^sub>i\<^sub>a\<^sub>b\<^sub>l\<^sub>e c) = ref)))"

	
	
\<comment>\<open>VDM source: derefOutput: (FMU * Ref -> Variable)
	derefOutput(fmu, ref) ==
(iota c in set ((fmu.io).LFoutput) & ((c.ref) = ref))
	pre (exists [c in set ((fmu.io).LFoutput)] & ((c.ref) = ref))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 327:5\<close>

\<comment>\<open>VDM source: pre_derefOutput: (FMU * Ref +> bool)
	pre_derefOutput(fmu, ref) ==
(exists [c in set ((fmu.io).LFoutput)] & ((c.ref) = ref))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 330:9\<close>
definition
	pre_derefOutput :: "FMU \<Rightarrow> Ref \<Rightarrow> bool"
where
	"pre_derefOutput fmu   ref \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `pre_derefOutput` specification.\<close>
		(inv_FMU fmu  \<and>  (inv_Ref ref))  \<and> 
		\<comment>\<open>User defined body of pre_derefOutput.\<close>
		(\<exists> c \<in> (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U fmu))  . ((ref\<^sub>V\<^sub>a\<^sub>r\<^sub>i\<^sub>a\<^sub>b\<^sub>l\<^sub>e c) = ref))"


\<comment>\<open>VDM source: post_derefOutput: (FMU * Ref * Variable +> bool)
	post_derefOutput(fmu, ref, RESULT) ==
null\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 327:5\<close>
definition
	post_derefOutput :: "FMU \<Rightarrow> Ref \<Rightarrow> Variable \<Rightarrow> bool"
where
	"post_derefOutput fmu   ref   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_derefOutput` specification.\<close>
		(inv_FMU fmu  \<and>  (inv_Ref ref)  \<and>  inv_Variable RESULT)"

definition
	derefOutput :: "FMU \<Rightarrow> Ref \<Rightarrow> Variable"
where
	"derefOutput fmu   ref \<equiv> 
	\<comment>\<open>User defined body of derefOutput.\<close>
	(THE c. (((c \<in>(LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U fmu)))) \<and> ((ref\<^sub>V\<^sub>a\<^sub>r\<^sub>i\<^sub>a\<^sub>b\<^sub>l\<^sub>e c) = ref)))"

	
	
\<comment>\<open>VDM source: Connections = map (FMURef) to (FMURef)
	inv cons == (((rng cons) inter (dom cons)) = {})\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 334:1\<close>
type_synonym Connections = "(FMURef \<rightharpoonup> FMURef)"
	

\<comment>\<open>VDM source: inv_Connections: (map (FMURef) to (FMURef) +> bool)
	inv_Connections(cons) ==
(((rng cons) inter (dom cons)) = {})\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 335:9\<close>
definition
	inv_Connections :: "Connections \<Rightarrow> bool"
where
	"inv_Connections cons \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `inv_Connections` specification.\<close>
		(((inv_Map inv_FMURef  inv_FMURef  cons)))  \<and> 
		\<comment>\<open>User defined body of inv_Connections.\<close>
		(((rng cons) \<inter> (dom cons)) = {})"
 
lemmas inv_Connections_defs = inv_Connections_def inv_FMURef_def inv_Map_defs inv_Name_def inv_Ref_def inv_VDMChar_def inv_VDMNat_def inv_VDMSeq1'_def inv_VDMSeq1'_defs 


	
	
\<comment>\<open>VDM source: ScenarioConnections = compose ScenarioConnections of dataConnections:Connections, clockConnections:Connections, timedClockConnections:map (Name) to (set1 of (FMURef)) end
	inv mk_ScenarioConnections(connections, clockConnections, timedClockConnections) == ((((dom clockConnections) inter (dom connections)) = {}) and ((((rng clockConnections) inter (rng connections)) = {}) and ((((rng clockConnections) inter (dunion (rng timedClockConnections))) = {}) and (((rng connections) inter (dunion (rng timedClockConnections))) = {}))))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 338:1\<close>
record ScenarioConnections = 
	dataConnections\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o\<^sub>C\<^sub>o\<^sub>n\<^sub>n\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n\<^sub>s :: "Connections"
		 
		 clockConnections\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o\<^sub>C\<^sub>o\<^sub>n\<^sub>n\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n\<^sub>s :: "Connections"
		 
		 timedClockConnections\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o\<^sub>C\<^sub>o\<^sub>n\<^sub>n\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n\<^sub>s :: "(Name \<rightharpoonup> FMURef VDMSet1)"
	

\<comment>\<open>VDM source: inv_ScenarioConnections: (ScenarioConnections +> bool)
	inv_ScenarioConnections(mk_ScenarioConnections(connections, clockConnections, timedClockConnections)) ==
((((dom clockConnections) inter (dom connections)) = {}) and ((((rng clockConnections) inter (rng connections)) = {}) and ((((rng clockConnections) inter (dunion (rng timedClockConnections))) = {}) and (((rng connections) inter (dunion (rng timedClockConnections))) = {}))))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 342:9\<close>
definition
	inv_ScenarioConnections :: "ScenarioConnections \<Rightarrow> bool"
where
	"inv_ScenarioConnections dummy0 \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `inv_ScenarioConnections` specification.\<close>
		( (((inv_Connections (dataConnections\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o\<^sub>C\<^sub>o\<^sub>n\<^sub>n\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n\<^sub>s dummy0))) \<and> 
		 ((inv_Connections (clockConnections\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o\<^sub>C\<^sub>o\<^sub>n\<^sub>n\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n\<^sub>s dummy0))) \<and> 
		 ((inv_Map (inv_Name) (inv_VDMSet1' inv_FMURef ) (timedClockConnections\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o\<^sub>C\<^sub>o\<^sub>n\<^sub>n\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n\<^sub>s dummy0))) ))  \<and> 
		\<comment>\<open>Implicit pattern context conversion\<close>
		(let connections = (dataConnections\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o\<^sub>C\<^sub>o\<^sub>n\<^sub>n\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n\<^sub>s dummy0); clockConnections = (clockConnections\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o\<^sub>C\<^sub>o\<^sub>n\<^sub>n\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n\<^sub>s dummy0); timedClockConnections = (timedClockConnections\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o\<^sub>C\<^sub>o\<^sub>n\<^sub>n\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n\<^sub>s dummy0) in 
		\<comment>\<open>User defined body of inv_ScenarioConnections.\<close>
		((((dom clockConnections) \<inter> (dom connections)) = {}) \<and> ((((rng clockConnections) \<inter> (rng connections)) = {}) \<and> ((((rng clockConnections) \<inter> (\<Union> (rng timedClockConnections))) = {}) \<and> (((rng connections) \<inter> (\<Union> (rng timedClockConnections))) = {})))))"

		
lemmas inv_ScenarioConnections_defs = inv_Connections_def inv_FMURef_def inv_Map_def inv_Map_defs inv_Name_def inv_Ref_def inv_ScenarioConnections_def inv_VDMChar_def inv_VDMNat_def inv_VDMSeq1'_def inv_VDMSeq1'_defs inv_VDMSet1'_def inv_VDMSet1'_defs 


	
	
\<comment>\<open>VDM source: Scenario = compose Scenario of fmus:map (Name) to (FMU), timeBasedClocks:set of (TimeBasedClock), connections:ScenarioConnections end
	inv mk_Scenario(fmus, timeBasedClocks, connections) == ((forall srcRef in set (dom (connections.dataConnections)) & (((srcRef.name) in set (dom fmus)) and let srcFMU:FMU = fmus((srcRef.name)), trgRef:FMURef = (connections.dataConnections)(srcRef) in ((exists [v in set ((srcFMU.io).LFoutput)] & ((srcRef.ref) = (v.ref))) and (((trgRef.name) in set (dom fmus)) and let trgFMU:FMU = fmus((trgRef.name)) in ((exists [v in set ((trgFMU.io).LFinput)] & ((trgRef.ref) = (v.ref))) and (pre_derefOutput(srcFMU, (srcRef.ref)) and (pre_derefInput(trgFMU, (trgRef.ref)) and let outputVar:Variable = derefOutput(srcFMU, (srcRef.ref)), inputVar:Variable = derefInput(trgFMU, (trgRef.ref)) in ((outputVar.type) = (inputVar.type))))))))) and ((forall fmuref in set (dom (connections.clockConnections)) & (((fmuref.name) in set (dom fmus)) and let fmu:FMU = fmus((fmuref.name)) in (exists [v in set (fmu.clocks)] & (((fmuref.ref) = (v.ref)) and (((v.type) = <output>) and ((v.interval) = <triggered>)))))) and ((forall fmuref in set (rng (connections.clockConnections)) & (((fmuref.name) in set (dom fmus)) and let fmu:FMU = fmus((fmuref.name)) in (exists [v in set (fmu.clocks)] & (((fmuref.ref) = (v.ref)) and (((v.type) = <input>) and ((v.interval) = <triggered>)))))) and (((dom (connections.timedClockConnections)) = {(c.name) | c in set timeBasedClocks}) and (forall t in set timeBasedClocks & (((t.master) in set (connections.timedClockConnections)((t.name))) and (forall c in set (dunion {c | c in set (rng (connections.timedClockConnections))}) & (pre_derefClock(fmus((c.name)), (c.ref)) and let clock:Clock = derefClock(fmus((c.name)), (c.ref)) in (((clock.interval) <> <triggered>) and ((clock.type) = <input>))))))))))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 353:5\<close>
record Scenario = 
	fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o :: "(Name \<rightharpoonup> FMU)"
		 
		 timeBasedClocks\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o :: "TimeBasedClock VDMSet"
		 
		 connections\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o :: "ScenarioConnections"
	

\<comment>\<open>VDM source: inv_Scenario: (Scenario +> bool)
	inv_Scenario(mk_Scenario(fmus, timeBasedClocks, connections)) ==
((forall srcRef in set (dom (connections.dataConnections)) & (((srcRef.name) in set (dom fmus)) and let srcFMU:FMU = fmus((srcRef.name)), trgRef:FMURef = (connections.dataConnections)(srcRef) in ((exists [v in set ((srcFMU.io).LFoutput)] & ((srcRef.ref) = (v.ref))) and (((trgRef.name) in set (dom fmus)) and let trgFMU:FMU = fmus((trgRef.name)) in ((exists [v in set ((trgFMU.io).LFinput)] & ((trgRef.ref) = (v.ref))) and (pre_derefOutput(srcFMU, (srcRef.ref)) and (pre_derefInput(trgFMU, (trgRef.ref)) and let outputVar:Variable = derefOutput(srcFMU, (srcRef.ref)), inputVar:Variable = derefInput(trgFMU, (trgRef.ref)) in ((outputVar.type) = (inputVar.type))))))))) and ((forall fmuref in set (dom (connections.clockConnections)) & (((fmuref.name) in set (dom fmus)) and let fmu:FMU = fmus((fmuref.name)) in (exists [v in set (fmu.clocks)] & (((fmuref.ref) = (v.ref)) and (((v.type) = <output>) and ((v.interval) = <triggered>)))))) and ((forall fmuref in set (rng (connections.clockConnections)) & (((fmuref.name) in set (dom fmus)) and let fmu:FMU = fmus((fmuref.name)) in (exists [v in set (fmu.clocks)] & (((fmuref.ref) = (v.ref)) and (((v.type) = <input>) and ((v.interval) = <triggered>)))))) and (((dom (connections.timedClockConnections)) = {(c.name) | c in set timeBasedClocks}) and (forall t in set timeBasedClocks & (((t.master) in set (connections.timedClockConnections)((t.name))) and (forall c in set (dunion {c | c in set (rng (connections.timedClockConnections))}) & (pre_derefClock(fmus((c.name)), (c.ref)) and let clock:Clock = derefClock(fmus((c.name)), (c.ref)) in (((clock.interval) <> <triggered>) and ((clock.type) = <input>))))))))))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 357:9\<close>
definition
	inv_Scenario :: "Scenario \<Rightarrow> bool"
where
	"inv_Scenario dummy0 \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `inv_Scenario` specification.\<close>
		( (((inv_Map (inv_Name) inv_FMU  (fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o dummy0))) \<and> 
		 ((inv_VDMSet' inv_TimeBasedClock  (timeBasedClocks\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o dummy0))) \<and> 
		 (inv_ScenarioConnections (connections\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o dummy0)) ))  \<and> 
		\<comment>\<open>Implicit pattern context conversion\<close>
		(let fmus = (fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o dummy0); timeBasedClocks = (timeBasedClocks\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o dummy0); connections = (connections\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o dummy0) in 
		\<comment>\<open>User defined body of inv_Scenario.\<close>
		((\<forall> srcRef \<in> (dom (dataConnections\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o\<^sub>C\<^sub>o\<^sub>n\<^sub>n\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n\<^sub>s connections))  . (((name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f srcRef) \<in> (dom fmus)) \<and> (
		let 
(srcFMU::FMU) = (the((fmus (name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f srcRef))))
		;
		
(trgRef::FMURef) = (the(((dataConnections\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o\<^sub>C\<^sub>o\<^sub>n\<^sub>n\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n\<^sub>s connections) srcRef)))
		in
			(if (inv_FMU srcFMU)
	 \<and> 
	(inv_FMURef trgRef) then
			((\<exists> v \<in> (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U srcFMU))  . ((ref\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f srcRef) = (ref\<^sub>V\<^sub>a\<^sub>r\<^sub>i\<^sub>a\<^sub>b\<^sub>l\<^sub>e v))) \<and> (((name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f trgRef) \<in> (dom fmus)) \<and> (
		let 
(trgFMU::FMU) = (the((fmus (name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f trgRef))))
		in
			(if (inv_FMU trgFMU) then
			((\<exists> v \<in> (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U trgFMU))  . ((ref\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f trgRef) = (ref\<^sub>V\<^sub>a\<^sub>r\<^sub>i\<^sub>a\<^sub>b\<^sub>l\<^sub>e v))) \<and> ((pre_derefOutput srcFMU   (ref\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f srcRef)) \<and> ((pre_derefInput trgFMU   (ref\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f trgRef)) \<and> (
		let 
(outputVar::Variable) = (derefOutput srcFMU   (ref\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f srcRef))
		;
		
(inputVar::Variable) = (derefInput trgFMU   (ref\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f trgRef))
		in
			(if (inv_Variable outputVar)
	 \<and> 
	(inv_Variable inputVar) then
			((type\<^sub>V\<^sub>a\<^sub>r\<^sub>i\<^sub>a\<^sub>b\<^sub>l\<^sub>e outputVar) = (type\<^sub>V\<^sub>a\<^sub>r\<^sub>i\<^sub>a\<^sub>b\<^sub>l\<^sub>e inputVar))
		 else
			undefined
		)
		))))
		 else
			undefined
		)
		)))
		 else
			undefined
		)
		))) \<and> ((\<forall> fmuref \<in> (dom (clockConnections\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o\<^sub>C\<^sub>o\<^sub>n\<^sub>n\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n\<^sub>s connections))  . (((name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f fmuref) \<in> (dom fmus)) \<and> (
		let 
(fmu::FMU) = (the((fmus (name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f fmuref))))
		in
			(if (inv_FMU fmu) then
			(\<exists>
		v \<in> (clocks\<^sub>F\<^sub>M\<^sub>U fmu)
		
		.
		(((ref\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f fmuref) = (ref\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k v)) \<and> (((type\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k v) = Causality.U_output ) \<and> ((interval\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k v) = Interval.U_triggered ))))
		 else
			undefined
		)
		))) \<and> ((\<forall> fmuref \<in> (rng (clockConnections\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o\<^sub>C\<^sub>o\<^sub>n\<^sub>n\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n\<^sub>s connections))  . (((name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f fmuref) \<in> (dom fmus)) \<and> (
		let 
(fmu::FMU) = (the((fmus (name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f fmuref))))
		in
			(if (inv_FMU fmu) then
			(\<exists>
		v \<in> (clocks\<^sub>F\<^sub>M\<^sub>U fmu)
		
		.
		(((ref\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f fmuref) = (ref\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k v)) \<and> (((type\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k v) = Causality.U_input ) \<and> ((interval\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k v) = Interval.U_triggered ))))
		 else
			undefined
		)
		))) \<and> (((dom (timedClockConnections\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o\<^sub>C\<^sub>o\<^sub>n\<^sub>n\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n\<^sub>s connections)) = { (name\<^sub>T\<^sub>i\<^sub>m\<^sub>e\<^sub>B\<^sub>a\<^sub>s\<^sub>e\<^sub>d\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k c) | c .  ((c \<in>timeBasedClocks))  }) \<and> (\<forall> t \<in> timeBasedClocks  . (((master\<^sub>T\<^sub>i\<^sub>m\<^sub>e\<^sub>B\<^sub>a\<^sub>s\<^sub>e\<^sub>d\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k t) \<in> ((timedClockConnections\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o\<^sub>C\<^sub>o\<^sub>n\<^sub>n\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n\<^sub>s connections) (name\<^sub>T\<^sub>i\<^sub>m\<^sub>e\<^sub>B\<^sub>a\<^sub>s\<^sub>e\<^sub>d\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k t))) \<and> (\<forall> c \<in> (\<Union> { c .   ((c \<in>(rng (timedClockConnections\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o\<^sub>C\<^sub>o\<^sub>n\<^sub>n\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n\<^sub>s connections))))  })  . ((pre_derefClock (fmus (name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f c))   (ref\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f c)) \<and> (
		let 
(clock::Clock) = (derefClock (fmus (name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f c))   (ref\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f c))
		in
			(if (inv_Clock clock) then
			(((interval\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k clock) \<noteq> Interval.U_triggered ) \<and> ((type\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k clock) = Causality.U_input ))
		 else
			undefined
		)
		))))))))))"
 
lemmas inv_Scenario_defs = inv_Causality_def inv_Clock_def inv_Connections_def inv_Contract_def inv_Environment_def inv_Equation_def inv_FMIValue_def inv_FMU_def inv_FMUMode_def inv_FMURef_def inv_IOLeo_def inv_Interval_def inv_Lambda_def inv_Map_def inv_Map_defs inv_Name_def inv_PortType_def inv_Real1_def inv_Ref_def inv_Scenario_def inv_ScenarioConnections_def inv_Time_def inv_TimeBasedClock_def inv_True_def inv_VDMChar_def inv_VDMNat_def inv_VDMReal_def inv_VDMSeq1'_def inv_VDMSeq1'_defs inv_VDMSet'_def inv_VDMSet'_defs inv_VDMSet1'_def inv_VDMSet1'_defs inv_ValueType_def inv_Variable_def inv_bool_def 


	
	
\<comment>\<open>VDM source: preSet: (FMU * Ref -> bool)
	preSet(fmu, input) ==
(exists1 v in set ((fmu.io).LFinput) & (((v.ref) = input) and (((v.causality) = <input>) and (((fmu.mode) <> <DONE>) and ((((fmu.mode) = <STEP>) => ((v.type) = <continous>)) and (((fmu.mode) = <EVENT>) => ((v.type) = <discrete>)))))))
	pre true\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 411:5\<close>

\<comment>\<open>VDM source: pre_preSet: (FMU * Ref +> bool)
	pre_preSet(fmu, input) ==
true\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 417:13\<close>
definition
	pre_preSet :: "FMU \<Rightarrow> Ref \<Rightarrow> bool"
where
	"pre_preSet fmu   input \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `pre_preSet` specification.\<close>
		(inv_FMU fmu  \<and>  (inv_Ref input))  \<and> 
		\<comment>\<open>User defined body of pre_preSet.\<close>
		(True::\<bool>)"


\<comment>\<open>VDM source: post_preSet: (FMU * Ref * bool +> bool)
	post_preSet(fmu, input, RESULT) ==
null\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 411:5\<close>
definition
	post_preSet :: "FMU \<Rightarrow> Ref \<Rightarrow> bool \<Rightarrow> bool"
where
	"post_preSet fmu   input   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_preSet` specification.\<close>
		(inv_FMU fmu  \<and>  (inv_Ref input)  \<and>  (inv_bool RESULT))"

definition
	preSet :: "FMU \<Rightarrow> Ref \<Rightarrow> bool"
where
	"preSet fmu   input \<equiv> 
	\<comment>\<open>User defined body of preSet.\<close>
	(\<exists>! v \<in> (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U fmu))  . (((ref\<^sub>V\<^sub>a\<^sub>r\<^sub>i\<^sub>a\<^sub>b\<^sub>l\<^sub>e v) = input) \<and> (((causality\<^sub>V\<^sub>a\<^sub>r\<^sub>i\<^sub>a\<^sub>b\<^sub>l\<^sub>e v) = Causality.U_input ) \<and> (((mode\<^sub>F\<^sub>M\<^sub>U fmu) \<noteq> FMUMode.U_DONE ) \<and> ((((mode\<^sub>F\<^sub>M\<^sub>U fmu) = FMUMode.U_STEP ) \<longrightarrow> ((type\<^sub>V\<^sub>a\<^sub>r\<^sub>i\<^sub>a\<^sub>b\<^sub>l\<^sub>e v) = PortType.U_continous )) \<and> (((mode\<^sub>F\<^sub>M\<^sub>U fmu) = FMUMode.U_EVENT ) \<longrightarrow> ((type\<^sub>V\<^sub>a\<^sub>r\<^sub>i\<^sub>a\<^sub>b\<^sub>l\<^sub>e v) = PortType.U_discrete )))))))"

	
	
\<comment>\<open>VDM source: set_m: (FMU * Ref * FMIValue +> FMU)
	set_m(fmu, ref, val) ==
mu(fmu, env |-> ((fmu.env) ++ {ref |-> val}))
	pre (pre_preSet(fmu, ref) and preSet(fmu, ref))
	post (((RESULT.mode) = (fmu.mode)) and (((RESULT.time) = (fmu.time)) and (((RESULT.io).LFinput) = ((fmu.io).LFinput))))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 420:5\<close>

\<comment>\<open>VDM source: pre_set_m: (FMU * Ref * FMIValue +> bool)
	pre_set_m(fmu, ref, val) ==
(pre_preSet(fmu, ref) and preSet(fmu, ref))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 424:30\<close>
definition
	pre_set_m :: "FMU \<Rightarrow> Ref \<Rightarrow> FMIValue \<Rightarrow> bool"
where
	"pre_set_m fmu   ref   val \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `pre_set_m` specification.\<close>
		(inv_FMU fmu  \<and>  (inv_Ref ref)  \<and>  inv_FMIValue val)  \<and> 
		\<comment>\<open>User defined body of pre_set_m.\<close>
		((pre_preSet fmu   ref) \<and> (preSet fmu   ref))"


\<comment>\<open>VDM source: post_set_m: (FMU * Ref * FMIValue * FMU +> bool)
	post_set_m(fmu, ref, val, RESULT) ==
(((RESULT.mode) = (fmu.mode)) and (((RESULT.time) = (fmu.time)) and (((RESULT.io).LFinput) = ((fmu.io).LFinput))))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 426:5\<close>
definition
	post_set_m :: "FMU \<Rightarrow> Ref \<Rightarrow> FMIValue \<Rightarrow> FMU \<Rightarrow> bool"
where
	"post_set_m fmu   ref   val   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `post_set_m` specification.\<close>
		(inv_FMU fmu  \<and>  (inv_Ref ref)  \<and>  inv_FMIValue val  \<and>  inv_FMU RESULT)  \<and> 
		\<comment>\<open>User defined body of post_set_m.\<close>
		(((mode\<^sub>F\<^sub>M\<^sub>U RESULT) = (mode\<^sub>F\<^sub>M\<^sub>U fmu)) \<and> (\<comment>\<open>Transform a VDM `=` expression into an `eq_Time` call\<close>
	(eq_Time (time\<^sub>F\<^sub>M\<^sub>U RESULT)   (time\<^sub>F\<^sub>M\<^sub>U fmu)) \<and> ((LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U RESULT)) = (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U fmu)))))"

definition
	set_m :: "FMU \<Rightarrow> Ref \<Rightarrow> FMIValue \<Rightarrow> FMU"
where
	"set_m fmu   ref   val \<equiv> 
	\<comment>\<open>User defined body of set_m.\<close>
	(fmu)\<lparr>env\<^sub>F\<^sub>M\<^sub>U := ((env\<^sub>F\<^sub>M\<^sub>U fmu) \<dagger> [ref\<mapsto>val])\<rparr>"

	
	
\<comment>\<open>VDM source: feedthroughSatisfied: (FMU * Variable -> bool)
	feedthroughSatisfied(fmu, outputVariable) ==
let inputs:set of (Variable) = {input | input in set ((fmu.io).LFinput) & ((input.ref) in set (outputVariable.dependsOn))} in (forall i in set inputs & (((i.ref) in set (dom (fmu.env))) and ((((i.contract) = <reactive>) => (((fmu.env)((i.ref)).time) >= (fmu.time))) and (((i.contract) = <delayed>) => (((fmu.env)((i.ref)).time) = (fmu.time))))))
	pre true\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 429:5\<close>

\<comment>\<open>VDM source: pre_feedthroughSatisfied: (FMU * Variable +> bool)
	pre_feedthroughSatisfied(fmu, outputVariable) ==
true\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 436:13\<close>
definition
	pre_feedthroughSatisfied :: "FMU \<Rightarrow> Variable \<Rightarrow> bool"
where
	"pre_feedthroughSatisfied fmu   outputVariable \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `pre_feedthroughSatisfied` specification.\<close>
		(inv_FMU fmu  \<and>  inv_Variable outputVariable)  \<and> 
		\<comment>\<open>User defined body of pre_feedthroughSatisfied.\<close>
		(True::\<bool>)"


\<comment>\<open>VDM source: post_feedthroughSatisfied: (FMU * Variable * bool +> bool)
	post_feedthroughSatisfied(fmu, outputVariable, RESULT) ==
null\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 429:5\<close>
definition
	post_feedthroughSatisfied :: "FMU \<Rightarrow> Variable \<Rightarrow> bool \<Rightarrow> bool"
where
	"post_feedthroughSatisfied fmu   outputVariable   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_feedthroughSatisfied` specification.\<close>
		(inv_FMU fmu  \<and>  inv_Variable outputVariable  \<and>  (inv_bool RESULT))"

definition
	feedthroughSatisfied :: "FMU \<Rightarrow> Variable \<Rightarrow> bool"
where
	"feedthroughSatisfied fmu   outputVariable \<equiv> 
	\<comment>\<open>User defined body of feedthroughSatisfied.\<close>
	(
		let 
(inputs::Variable VDMSet) = { input .   ((input \<in>(LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U fmu))))  \<and> ((ref\<^sub>V\<^sub>a\<^sub>r\<^sub>i\<^sub>a\<^sub>b\<^sub>l\<^sub>e input) \<in> (dependsOn\<^sub>V\<^sub>a\<^sub>r\<^sub>i\<^sub>a\<^sub>b\<^sub>l\<^sub>e outputVariable)) }
		in
			(if ((inv_VDMSet' inv_Variable  inputs)) then
			(\<forall>
		i \<in> inputs
		
		.
		(((ref\<^sub>V\<^sub>a\<^sub>r\<^sub>i\<^sub>a\<^sub>b\<^sub>l\<^sub>e i) \<in> (dom (env\<^sub>F\<^sub>M\<^sub>U fmu))) \<and> ((((contract\<^sub>V\<^sub>a\<^sub>r\<^sub>i\<^sub>a\<^sub>b\<^sub>l\<^sub>e i) = Contract.U_reactive ) \<longrightarrow> \<comment>\<open>Transform a VDM `>` expression into a reversed `ord_Time` call\<close>
	(ord_Time (time\<^sub>F\<^sub>M\<^sub>U fmu)   (time\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e (the(((env\<^sub>F\<^sub>M\<^sub>U fmu) (ref\<^sub>V\<^sub>a\<^sub>r\<^sub>i\<^sub>a\<^sub>b\<^sub>l\<^sub>e i)))))) \<or> 
	\<comment>\<open>Transform a VDM `=` expression into an `eq_Time` call\<close>
	(eq_Time (time\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e (the(((env\<^sub>F\<^sub>M\<^sub>U fmu) (ref\<^sub>V\<^sub>a\<^sub>r\<^sub>i\<^sub>a\<^sub>b\<^sub>l\<^sub>e i)))))   (time\<^sub>F\<^sub>M\<^sub>U fmu))) \<and> (((contract\<^sub>V\<^sub>a\<^sub>r\<^sub>i\<^sub>a\<^sub>b\<^sub>l\<^sub>e i) = Contract.U_delayed ) \<longrightarrow> \<comment>\<open>Transform a VDM `=` expression into an `eq_Time` call\<close>
	(eq_Time (time\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e (the(((env\<^sub>F\<^sub>M\<^sub>U fmu) (ref\<^sub>V\<^sub>a\<^sub>r\<^sub>i\<^sub>a\<^sub>b\<^sub>l\<^sub>e i)))))   (time\<^sub>F\<^sub>M\<^sub>U fmu))))))
		 else
			undefined
		)
		)"

	
	
\<comment>\<open>VDM source: preGet: (FMU * Ref -> bool)
	preGet(fmu, ref) ==
let outputVariable:Variable = derefOutput(fmu, ref) in ((exists1 v in set ((fmu.io).LFoutput) & (((v.ref) = ref) and ((v.causality) = <output>))) and (((fmu.mode) <> <DONE>) and (pre_feedthroughSatisfied(fmu, outputVariable) and feedthroughSatisfied(fmu, outputVariable))))
	pre pre_derefOutput(fmu, ref)\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 438:5\<close>

\<comment>\<open>VDM source: pre_preGet: (FMU * Ref +> bool)
	pre_preGet(fmu, ref) ==
pre_derefOutput(fmu, ref)\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 446:9\<close>
definition
	pre_preGet :: "FMU \<Rightarrow> Ref \<Rightarrow> bool"
where
	"pre_preGet fmu   ref \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `pre_preGet` specification.\<close>
		(inv_FMU fmu  \<and>  (inv_Ref ref))  \<and> 
		\<comment>\<open>User defined body of pre_preGet.\<close>
		(pre_derefOutput fmu   ref)"


\<comment>\<open>VDM source: post_preGet: (FMU * Ref * bool +> bool)
	post_preGet(fmu, ref, RESULT) ==
null\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 438:5\<close>
definition
	post_preGet :: "FMU \<Rightarrow> Ref \<Rightarrow> bool \<Rightarrow> bool"
where
	"post_preGet fmu   ref   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_preGet` specification.\<close>
		(inv_FMU fmu  \<and>  (inv_Ref ref)  \<and>  (inv_bool RESULT))"

definition
	preGet :: "FMU \<Rightarrow> Ref \<Rightarrow> bool"
where
	"preGet fmu   ref \<equiv> 
	\<comment>\<open>User defined body of preGet.\<close>
	(
		let 
(outputVariable::Variable) = (derefOutput fmu   ref)
		in
			(if (inv_Variable outputVariable) then
			((\<exists>! v \<in> (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U fmu))  . (((ref\<^sub>V\<^sub>a\<^sub>r\<^sub>i\<^sub>a\<^sub>b\<^sub>l\<^sub>e v) = ref) \<and> ((causality\<^sub>V\<^sub>a\<^sub>r\<^sub>i\<^sub>a\<^sub>b\<^sub>l\<^sub>e v) = Causality.U_output ))) \<and> (((mode\<^sub>F\<^sub>M\<^sub>U fmu) \<noteq> FMUMode.U_DONE ) \<and> ((pre_feedthroughSatisfied fmu   outputVariable) \<and> (feedthroughSatisfied fmu   outputVariable))))
		 else
			undefined
		)
		)"

	
	
\<comment>\<open>VDM source: get_m: (FMU * Ref +> (FMU * FMIValue))
	get_m(fmu, ref) ==
mk_(fmu, (fmu.env)(ref))
	pre (preGet(fmu, ref) and pre_preGet(fmu, ref))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 449:5\<close>

\<comment>\<open>VDM source: pre_get_m: (FMU * Ref +> bool)
	pre_get_m(fmu, ref) ==
(preGet(fmu, ref) and pre_preGet(fmu, ref))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 453:26\<close>
definition
	pre_get_m :: "FMU \<Rightarrow> Ref \<Rightarrow> bool"
where
	"pre_get_m fmu   ref \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `pre_get_m` specification.\<close>
		(inv_FMU fmu  \<and>  (inv_Ref ref))  \<and> 
		\<comment>\<open>User defined body of pre_get_m.\<close>
		((preGet fmu   ref) \<and> (pre_preGet fmu   ref))"


\<comment>\<open>VDM source: post_get_m: (FMU * Ref * (FMU * FMIValue) +> bool)
	post_get_m(fmu, ref, RESULT) ==
null\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 449:5\<close>
definition
	post_get_m :: "FMU \<Rightarrow> Ref \<Rightarrow> (FMU \<times> FMIValue) \<Rightarrow> bool"
where
	"post_get_m fmu   ref   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_get_m` specification.\<close>
		(inv_FMU fmu  \<and>  (inv_Ref ref)  \<and>  
		(inv_FMU (fst RESULT)\<and>
		 inv_FMIValue (snd RESULT)
		))"

definition
	get_m :: "FMU \<Rightarrow> Ref \<Rightarrow> (FMU \<times> FMIValue)"
where
	"get_m fmu   ref \<equiv> 
	\<comment>\<open>User defined body of get_m.\<close>
	(fmu , ((env\<^sub>F\<^sub>M\<^sub>U fmu) ref))"

	
	
\<comment>\<open>VDM source: preSetC: (FMU * Ref * bool -> bool)
	preSetC(fmu, clock, val) ==
(((exists1 v in set (fmu.clocks) & (((v.ref) = clock) and ((v.type) = <input>))) and val) <=> ((not (clock in set (fmu.activeClocks))) and ((fmu.mode) = <EVENT>)))
	pre true\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 456:5\<close>

\<comment>\<open>VDM source: pre_preSetC: (FMU * Ref * bool +> bool)
	pre_preSetC(fmu, clock, val) ==
true\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 461:13\<close>
definition
	pre_preSetC :: "FMU \<Rightarrow> Ref \<Rightarrow> bool \<Rightarrow> bool"
where
	"pre_preSetC fmu   clock   val \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `pre_preSetC` specification.\<close>
		(inv_FMU fmu  \<and>  (inv_Ref clock)  \<and>  (inv_bool val))  \<and> 
		\<comment>\<open>User defined body of pre_preSetC.\<close>
		(True::\<bool>)"


\<comment>\<open>VDM source: post_preSetC: (FMU * Ref * bool * bool +> bool)
	post_preSetC(fmu, clock, val, RESULT) ==
null\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 456:5\<close>
definition
	post_preSetC :: "FMU \<Rightarrow> Ref \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool"
where
	"post_preSetC fmu   clock   val   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_preSetC` specification.\<close>
		(inv_FMU fmu  \<and>  (inv_Ref clock)  \<and>  (inv_bool val)  \<and>  (inv_bool RESULT))"

definition
	preSetC :: "FMU \<Rightarrow> Ref \<Rightarrow> bool \<Rightarrow> bool"
where
	"preSetC fmu   clock   val \<equiv> 
	\<comment>\<open>User defined body of preSetC.\<close>
	(((\<exists>! v \<in> (clocks\<^sub>F\<^sub>M\<^sub>U fmu)  . (((ref\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k v) = clock) \<and> ((type\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k v) = Causality.U_input ))) \<and> val) \<longleftrightarrow> ((\<not> (clock \<in> (activeClocks\<^sub>F\<^sub>M\<^sub>U fmu))) \<and> ((mode\<^sub>F\<^sub>M\<^sub>U fmu) = FMUMode.U_EVENT )))"

	
	
\<comment>\<open>VDM source: set_cm: (FMU * Ref * bool +> FMU)
	set_cm(fmu, ref, val) ==
mu(fmu, env |-> ((fmu.env) ++ {ref |-> mk_FMIValue(val, (fmu.time))}), activeClocks |-> (if val
then ((fmu.activeClocks) union {ref})
else ((fmu.activeClocks) \ {ref})))
	pre (preSetC(fmu, ref, val) and pre_preSetC(fmu, ref, val))
	post (val <=> (ref in set (RESULT.activeClocks)))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 463:5\<close>

\<comment>\<open>VDM source: pre_set_cm: (FMU * Ref * bool +> bool)
	pre_set_cm(fmu, ref, val) ==
(preSetC(fmu, ref, val) and pre_preSetC(fmu, ref, val))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 468:32\<close>
definition
	pre_set_cm :: "FMU \<Rightarrow> Ref \<Rightarrow> bool \<Rightarrow> bool"
where
	"pre_set_cm fmu   ref   val \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `pre_set_cm` specification.\<close>
		(inv_FMU fmu  \<and>  (inv_Ref ref)  \<and>  (inv_bool val))  \<and> 
		\<comment>\<open>User defined body of pre_set_cm.\<close>
		((preSetC fmu   ref   val) \<and> (pre_preSetC fmu   ref   val))"


\<comment>\<open>VDM source: post_set_cm: (FMU * Ref * bool * FMU +> bool)
	post_set_cm(fmu, ref, val, RESULT) ==
(val <=> (ref in set (RESULT.activeClocks)))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 469:14\<close>
definition
	post_set_cm :: "FMU \<Rightarrow> Ref \<Rightarrow> bool \<Rightarrow> FMU \<Rightarrow> bool"
where
	"post_set_cm fmu   ref   val   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `post_set_cm` specification.\<close>
		(inv_FMU fmu  \<and>  (inv_Ref ref)  \<and>  (inv_bool val)  \<and>  inv_FMU RESULT)  \<and> 
		\<comment>\<open>User defined body of post_set_cm.\<close>
		(val \<longleftrightarrow> (ref \<in> (activeClocks\<^sub>F\<^sub>M\<^sub>U RESULT)))"

definition
	set_cm :: "FMU \<Rightarrow> Ref \<Rightarrow> bool \<Rightarrow> FMU"
where
	"set_cm fmu   ref   val \<equiv> 
	\<comment>\<open>User defined body of set_cm.\<close>
	(fmu)\<lparr>env\<^sub>F\<^sub>M\<^sub>U := ((env\<^sub>F\<^sub>M\<^sub>U fmu) \<dagger> [ref\<mapsto>\<lparr>fmiValue\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e = ValueType.U_bool val, time\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e = (time\<^sub>F\<^sub>M\<^sub>U fmu)\<rparr>]), activeClocks\<^sub>F\<^sub>M\<^sub>U := (
		if (val) then
		(((activeClocks\<^sub>F\<^sub>M\<^sub>U fmu) \<union> {ref}))
		else
		(((activeClocks\<^sub>F\<^sub>M\<^sub>U fmu) - {ref})))\<rparr>"

	
	
\<comment>\<open>VDM source: preGetC: (FMU * Ref -> bool)
	preGetC(fmu, clock) ==
((exists1 v in set (fmu.clocks) & (((v.ref) = clock) and ((v.type) = <output>))) and ((fmu.mode) = <EVENT>))
	pre true\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 471:5\<close>

\<comment>\<open>VDM source: pre_preGetC: (FMU * Ref +> bool)
	pre_preGetC(fmu, clock) ==
true\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 475:13\<close>
definition
	pre_preGetC :: "FMU \<Rightarrow> Ref \<Rightarrow> bool"
where
	"pre_preGetC fmu   clock \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `pre_preGetC` specification.\<close>
		(inv_FMU fmu  \<and>  (inv_Ref clock))  \<and> 
		\<comment>\<open>User defined body of pre_preGetC.\<close>
		(True::\<bool>)"


\<comment>\<open>VDM source: post_preGetC: (FMU * Ref * bool +> bool)
	post_preGetC(fmu, clock, RESULT) ==
null\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 471:5\<close>
definition
	post_preGetC :: "FMU \<Rightarrow> Ref \<Rightarrow> bool \<Rightarrow> bool"
where
	"post_preGetC fmu   clock   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_preGetC` specification.\<close>
		(inv_FMU fmu  \<and>  (inv_Ref clock)  \<and>  (inv_bool RESULT))"

definition
	preGetC :: "FMU \<Rightarrow> Ref \<Rightarrow> bool"
where
	"preGetC fmu   clock \<equiv> 
	\<comment>\<open>User defined body of preGetC.\<close>
	((\<exists>! v \<in> (clocks\<^sub>F\<^sub>M\<^sub>U fmu)  . (((ref\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k v) = clock) \<and> ((type\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k v) = Causality.U_output ))) \<and> ((mode\<^sub>F\<^sub>M\<^sub>U fmu) = FMUMode.U_EVENT ))"

	
	
\<comment>\<open>VDM source: get_cm: (FMU * Ref +> (FMU * FMIValue))
	get_cm(fmu, ref) ==
mk_(fmu, (fmu.env)(ref))
	pre (preGetC(fmu, ref) and pre_preGetC(fmu, ref))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 477:5\<close>

\<comment>\<open>VDM source: pre_get_cm: (FMU * Ref +> bool)
	pre_get_cm(fmu, ref) ==
(preGetC(fmu, ref) and pre_preGetC(fmu, ref))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 480:27\<close>
definition
	pre_get_cm :: "FMU \<Rightarrow> Ref \<Rightarrow> bool"
where
	"pre_get_cm fmu   ref \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `pre_get_cm` specification.\<close>
		(inv_FMU fmu  \<and>  (inv_Ref ref))  \<and> 
		\<comment>\<open>User defined body of pre_get_cm.\<close>
		((preGetC fmu   ref) \<and> (pre_preGetC fmu   ref))"


\<comment>\<open>VDM source: post_get_cm: (FMU * Ref * (FMU * FMIValue) +> bool)
	post_get_cm(fmu, ref, RESULT) ==
null\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 477:5\<close>
definition
	post_get_cm :: "FMU \<Rightarrow> Ref \<Rightarrow> (FMU \<times> FMIValue) \<Rightarrow> bool"
where
	"post_get_cm fmu   ref   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_get_cm` specification.\<close>
		(inv_FMU fmu  \<and>  (inv_Ref ref)  \<and>  
		(inv_FMU (fst RESULT)\<and>
		 inv_FMIValue (snd RESULT)
		))"

definition
	get_cm :: "FMU \<Rightarrow> Ref \<Rightarrow> (FMU \<times> FMIValue)"
where
	"get_cm fmu   ref \<equiv> 
	\<comment>\<open>User defined body of get_cm.\<close>
	(fmu , ((env\<^sub>F\<^sub>M\<^sub>U fmu) ref))"

	
	
\<comment>\<open>VDM source: preStepT: (FMU * Real1 -> bool)
	preStepT(fmu, stepSize) ==
let continousInputs:set of (Variable) = {i | i in set ((fmu.io).LFinput) & ((i.type) = <continous>)} in ((forall i in set continousInputs & ((((i.contract) = <reactive>) => ((((fmu.env)((i.ref)).time).r) = (((fmu.time).r) + stepSize))) and (((i.contract) = <delayed>) => (((fmu.env)((i.ref)).time) = (fmu.time))))) and ((fmu.mode) = <STEP>))
	pre true\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 483:5\<close>

\<comment>\<open>VDM source: pre_preStepT: (FMU * Real1 +> bool)
	pre_preStepT(fmu, stepSize) ==
true\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 490:13\<close>
definition
	pre_preStepT :: "FMU \<Rightarrow> Real1 \<Rightarrow> bool"
where
	"pre_preStepT fmu   stepSize \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `pre_preStepT` specification.\<close>
		(inv_FMU fmu  \<and>  (inv_Real1 stepSize))  \<and> 
		\<comment>\<open>User defined body of pre_preStepT.\<close>
		(True::\<bool>)"


\<comment>\<open>VDM source: post_preStepT: (FMU * Real1 * bool +> bool)
	post_preStepT(fmu, stepSize, RESULT) ==
null\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 483:5\<close>
definition
	post_preStepT :: "FMU \<Rightarrow> Real1 \<Rightarrow> bool \<Rightarrow> bool"
where
	"post_preStepT fmu   stepSize   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_preStepT` specification.\<close>
		(inv_FMU fmu  \<and>  (inv_Real1 stepSize)  \<and>  (inv_bool RESULT))"

definition
	preStepT :: "FMU \<Rightarrow> Real1 \<Rightarrow> bool"
where
	"preStepT fmu   stepSize \<equiv> 
	\<comment>\<open>User defined body of preStepT.\<close>
	(
		let 
(continousInputs::Variable VDMSet) = { i .   ((i \<in>(LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U fmu))))  \<and> ((type\<^sub>V\<^sub>a\<^sub>r\<^sub>i\<^sub>a\<^sub>b\<^sub>l\<^sub>e i) = PortType.U_continous ) }
		in
			(if ((inv_VDMSet' inv_Variable  continousInputs)) then
			((\<forall> i \<in> continousInputs  . ((((contract\<^sub>V\<^sub>a\<^sub>r\<^sub>i\<^sub>a\<^sub>b\<^sub>l\<^sub>e i) = Contract.U_reactive ) \<longrightarrow> ((r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e (the(((env\<^sub>F\<^sub>M\<^sub>U fmu) (ref\<^sub>V\<^sub>a\<^sub>r\<^sub>i\<^sub>a\<^sub>b\<^sub>l\<^sub>e i)))))) = ((r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U fmu)) + stepSize))) \<and> (((contract\<^sub>V\<^sub>a\<^sub>r\<^sub>i\<^sub>a\<^sub>b\<^sub>l\<^sub>e i) = Contract.U_delayed ) \<longrightarrow> \<comment>\<open>Transform a VDM `=` expression into an `eq_Time` call\<close>
	(eq_Time (time\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e (the(((env\<^sub>F\<^sub>M\<^sub>U fmu) (ref\<^sub>V\<^sub>a\<^sub>r\<^sub>i\<^sub>a\<^sub>b\<^sub>l\<^sub>e i)))))   (time\<^sub>F\<^sub>M\<^sub>U fmu))))) \<and> ((mode\<^sub>F\<^sub>M\<^sub>U fmu) = FMUMode.U_STEP ))
		 else
			undefined
		)
		)"

	
	
\<comment>\<open>VDM source: postStepT: (FMU * Real1 * bool * FMU * Real1 -> bool)
	postStepT(fmu, stepTaken, eventTriggered, oldFMU, stepAsked) ==
(((stepTaken <= stepAsked) and ((stepTaken <= (oldFMU.maxStep)) and eventTriggered)) <=> (((oldFMU.maxStep) <= stepTaken) and ((((fmu.time).r) = (((oldFMU.time).r) + stepTaken)) and (((fmu.time).i) = ((oldFMU.time).i)))))
	pre true\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 493:5\<close>

\<comment>\<open>VDM source: pre_postStepT: (FMU * Real1 * bool * FMU * Real1 +> bool)
	pre_postStepT(fmu, stepTaken, eventTriggered, oldFMU, stepAsked) ==
true\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 500:9\<close>
definition
	pre_postStepT :: "FMU \<Rightarrow> Real1 \<Rightarrow> bool \<Rightarrow> FMU \<Rightarrow> Real1 \<Rightarrow> bool"
where
	"pre_postStepT fmu   stepTaken   eventTriggered   oldFMU   stepAsked \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `pre_postStepT` specification.\<close>
		(inv_FMU fmu  \<and>  (inv_Real1 stepTaken)  \<and>  (inv_bool eventTriggered)  \<and>  inv_FMU oldFMU  \<and>  (inv_Real1 stepAsked))  \<and> 
		\<comment>\<open>User defined body of pre_postStepT.\<close>
		(True::\<bool>)"


\<comment>\<open>VDM source: post_postStepT: (FMU * Real1 * bool * FMU * Real1 * bool +> bool)
	post_postStepT(fmu, stepTaken, eventTriggered, oldFMU, stepAsked, RESULT) ==
null\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 493:5\<close>
definition
	post_postStepT :: "FMU \<Rightarrow> Real1 \<Rightarrow> bool \<Rightarrow> FMU \<Rightarrow> Real1 \<Rightarrow> bool \<Rightarrow> bool"
where
	"post_postStepT fmu   stepTaken   eventTriggered   oldFMU   stepAsked   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_postStepT` specification.\<close>
		(inv_FMU fmu  \<and>  (inv_Real1 stepTaken)  \<and>  (inv_bool eventTriggered)  \<and>  inv_FMU oldFMU  \<and>  (inv_Real1 stepAsked)  \<and>  (inv_bool RESULT))"

definition
	postStepT :: "FMU \<Rightarrow> Real1 \<Rightarrow> bool \<Rightarrow> FMU \<Rightarrow> Real1 \<Rightarrow> bool"
where
	"postStepT fmu   stepTaken   eventTriggered   oldFMU   stepAsked \<equiv> 
	\<comment>\<open>User defined body of postStepT.\<close>
	(((stepTaken \<le> stepAsked) \<and> ((stepTaken \<le> (maxStep\<^sub>F\<^sub>M\<^sub>U oldFMU)) \<and> eventTriggered)) \<longleftrightarrow> (((maxStep\<^sub>F\<^sub>M\<^sub>U oldFMU) \<le> stepTaken) \<and> (((r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U fmu)) = ((r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U oldFMU)) + stepTaken)) \<and> ((i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U fmu)) = (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U oldFMU))))))"

	
	
\<comment>\<open>VDM source: updateOutputs: (FMU * Time -> Environment)
	updateOutputs(fmu, time) ==
let outputRef:set of (Ref) = {(outputVar.ref) | outputVar in set ((fmu.io).LFoutput)} in {oValue |-> calculate(oValue, (fmu.env), time) | oValue in set ((dom (fmu.env)) inter outputRef) & pre_calculate(oValue, (fmu.env), time)}
	pre true\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 505:5\<close>

\<comment>\<open>VDM source: pre_updateOutputs: (FMU * Time +> bool)
	pre_updateOutputs(fmu, time) ==
true\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 509:9\<close>
definition
	pre_updateOutputs :: "FMU \<Rightarrow> Time \<Rightarrow> bool"
where
	"pre_updateOutputs fmu   time \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `pre_updateOutputs` specification.\<close>
		(inv_FMU fmu  \<and>  inv_Time time)  \<and> 
		\<comment>\<open>User defined body of pre_updateOutputs.\<close>
		(True::\<bool>)"


\<comment>\<open>VDM source: post_updateOutputs: (FMU * Time * Environment +> bool)
	post_updateOutputs(fmu, time, RESULT) ==
null\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 505:5\<close>
definition
	post_updateOutputs :: "FMU \<Rightarrow> Time \<Rightarrow> Environment \<Rightarrow> bool"
where
	"post_updateOutputs fmu   time   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_updateOutputs` specification.\<close>
		(inv_FMU fmu  \<and>  inv_Time time  \<and>  (inv_Environment RESULT))"

definition
	updateOutputs :: "FMU \<Rightarrow> Time \<Rightarrow> Environment"
where
	"updateOutputs fmu   time \<equiv> 
	\<comment>\<open>User defined body of updateOutputs.\<close>
	(
		let 
(outputRef::Ref VDMSet) = { (ref\<^sub>V\<^sub>a\<^sub>r\<^sub>i\<^sub>a\<^sub>b\<^sub>l\<^sub>e outputVar) | outputVar .  ((outputVar \<in>(LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U fmu))))  }
		in
			(if ((inv_VDMSet' ((inv_VDMNat)) outputRef)) then
			(\<comment>\<open>VDM Map comprehension is translated as a lambda-term through mapCompSetBound\<close>
		mapCompSetBound 
		{ oValue .   ((oValue \<in>((dom (env\<^sub>F\<^sub>M\<^sub>U fmu)) \<inter> outputRef)))  \<and> (pre_calculate oValue   (env\<^sub>F\<^sub>M\<^sub>U fmu)   time) } 
		{ (calculate oValue   (env\<^sub>F\<^sub>M\<^sub>U fmu)   time) | (dummy0RANGE :: FMIValue) .  \<comment>\<open>Type bound set compression will generate a (possibly spurious, i.e. inv_VDMSet') difficult set finiteness proof!!!\<close>  (( ((((case (fmiValue\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e dummy0RANGE) of
		 ValueType.U_bool (fmiValue\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e dummy0RANGE) \<Rightarrow> (inv_bool (fmiValue\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e dummy0RANGE))
		  | ValueType.U_VDMReal (fmiValue\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e dummy0RANGE) \<Rightarrow> (inv_VDMReal (fmiValue\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e dummy0RANGE))
		 ))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e dummy0RANGE))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e dummy0RANGE)))) )) )))  \<and> (pre_calculate oValue   (env\<^sub>F\<^sub>M\<^sub>U fmu)   time) } 
		(inv_VDMNat) 
		 ((((case (fmiValue\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e FMIValue) of
		 ValueType.U_bool (fmiValue\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e FMIValue) \<Rightarrow> (inv_bool (fmiValue\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e FMIValue))
		  | ValueType.U_VDMReal (fmiValue\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e FMIValue) \<Rightarrow> (inv_VDMReal (fmiValue\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e FMIValue))
		 ))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e FMIValue))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e FMIValue)))) )) ) 
		(domid ) 
		(
	\<lambda> (dummy0DOMAIN :: VDMNat)   (dummy0RANGE :: FMIValue) .
		(if (((inv_VDMNat dummy0DOMAIN)))  \<and>  (( ((((case (fmiValue\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e dummy0RANGE) of
		 ValueType.U_bool (fmiValue\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e dummy0RANGE) \<Rightarrow> (inv_bool (fmiValue\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e dummy0RANGE))
		  | ValueType.U_VDMReal (fmiValue\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e dummy0RANGE) \<Rightarrow> (inv_VDMReal (fmiValue\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e dummy0RANGE))
		 ))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e dummy0RANGE))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e dummy0RANGE)))) )) ))) \<and>  ((((case (fmiValue\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e (
		if ((\<exists> (dummy0RANGE :: FMIValue)  . ((( ((((case (fmiValue\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e dummy0RANGE) of
		 ValueType.U_bool (fmiValue\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e dummy0RANGE) \<Rightarrow> (inv_bool (fmiValue\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e dummy0RANGE))
		  | ValueType.U_VDMReal (fmiValue\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e dummy0RANGE) \<Rightarrow> (inv_VDMReal (fmiValue\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e dummy0RANGE))
		 ))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e dummy0RANGE))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e dummy0RANGE)))) )) ))) \<longrightarrow> (\<comment>\<open>Transform a VDM `=` expression into an `eq_FMIValue` call\<close>
	(eq_FMIValue dummy0RANGE   (calculate oValue   (env\<^sub>F\<^sub>M\<^sub>U fmu)   time)) \<and> (pre_calculate oValue   (env\<^sub>F\<^sub>M\<^sub>U fmu)   time))))) then
		(dummy0RANGE)
		else
		(undefined))) of
		 ValueType.U_bool (fmiValue\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e (
		if ((\<exists> (dummy0RANGE :: FMIValue)  . ((( ((((case (fmiValue\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e dummy0RANGE) of
		 ValueType.U_bool (fmiValue\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e dummy0RANGE) \<Rightarrow> (inv_bool (fmiValue\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e dummy0RANGE))
		  | ValueType.U_VDMReal (fmiValue\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e dummy0RANGE) \<Rightarrow> (inv_VDMReal (fmiValue\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e dummy0RANGE))
		 ))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e dummy0RANGE))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e dummy0RANGE)))) )) ))) \<longrightarrow> (\<comment>\<open>Transform a VDM `=` expression into an `eq_FMIValue` call\<close>
	(eq_FMIValue dummy0RANGE   (calculate oValue   (env\<^sub>F\<^sub>M\<^sub>U fmu)   time)) \<and> (pre_calculate oValue   (env\<^sub>F\<^sub>M\<^sub>U fmu)   time))))) then
		(dummy0RANGE)
		else
		(undefined))) \<Rightarrow> (inv_bool (fmiValue\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e (
		if ((\<exists> (dummy0RANGE :: FMIValue)  . ((( ((((case (fmiValue\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e dummy0RANGE) of
		 ValueType.U_bool (fmiValue\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e dummy0RANGE) \<Rightarrow> (inv_bool (fmiValue\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e dummy0RANGE))
		  | ValueType.U_VDMReal (fmiValue\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e dummy0RANGE) \<Rightarrow> (inv_VDMReal (fmiValue\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e dummy0RANGE))
		 ))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e dummy0RANGE))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e dummy0RANGE)))) )) ))) \<longrightarrow> (\<comment>\<open>Transform a VDM `=` expression into an `eq_FMIValue` call\<close>
	(eq_FMIValue dummy0RANGE   (calculate oValue   (env\<^sub>F\<^sub>M\<^sub>U fmu)   time)) \<and> (pre_calculate oValue   (env\<^sub>F\<^sub>M\<^sub>U fmu)   time))))) then
		(dummy0RANGE)
		else
		(undefined))))
		  | ValueType.U_VDMReal (fmiValue\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e (
		if ((\<exists> (dummy0RANGE :: FMIValue)  . ((( ((((case (fmiValue\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e dummy0RANGE) of
		 ValueType.U_bool (fmiValue\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e dummy0RANGE) \<Rightarrow> (inv_bool (fmiValue\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e dummy0RANGE))
		  | ValueType.U_VDMReal (fmiValue\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e dummy0RANGE) \<Rightarrow> (inv_VDMReal (fmiValue\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e dummy0RANGE))
		 ))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e dummy0RANGE))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e dummy0RANGE)))) )) ))) \<longrightarrow> (\<comment>\<open>Transform a VDM `=` expression into an `eq_FMIValue` call\<close>
	(eq_FMIValue dummy0RANGE   (calculate oValue   (env\<^sub>F\<^sub>M\<^sub>U fmu)   time)) \<and> (pre_calculate oValue   (env\<^sub>F\<^sub>M\<^sub>U fmu)   time))))) then
		(dummy0RANGE)
		else
		(undefined))) \<Rightarrow> (inv_VDMReal (fmiValue\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e (
		if ((\<exists> (dummy0RANGE :: FMIValue)  . ((( ((((case (fmiValue\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e dummy0RANGE) of
		 ValueType.U_bool (fmiValue\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e dummy0RANGE) \<Rightarrow> (inv_bool (fmiValue\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e dummy0RANGE))
		  | ValueType.U_VDMReal (fmiValue\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e dummy0RANGE) \<Rightarrow> (inv_VDMReal (fmiValue\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e dummy0RANGE))
		 ))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e dummy0RANGE))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e dummy0RANGE)))) )) ))) \<longrightarrow> (\<comment>\<open>Transform a VDM `=` expression into an `eq_FMIValue` call\<close>
	(eq_FMIValue dummy0RANGE   (calculate oValue   (env\<^sub>F\<^sub>M\<^sub>U fmu)   time)) \<and> (pre_calculate oValue   (env\<^sub>F\<^sub>M\<^sub>U fmu)   time))))) then
		(dummy0RANGE)
		else
		(undefined))))
		 ))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e (
		if ((\<exists> (dummy0RANGE :: FMIValue)  . ((( ((((case (fmiValue\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e dummy0RANGE) of
		 ValueType.U_bool (fmiValue\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e dummy0RANGE) \<Rightarrow> (inv_bool (fmiValue\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e dummy0RANGE))
		  | ValueType.U_VDMReal (fmiValue\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e dummy0RANGE) \<Rightarrow> (inv_VDMReal (fmiValue\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e dummy0RANGE))
		 ))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e dummy0RANGE))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e dummy0RANGE)))) )) ))) \<longrightarrow> (\<comment>\<open>Transform a VDM `=` expression into an `eq_FMIValue` call\<close>
	(eq_FMIValue dummy0RANGE   (calculate oValue   (env\<^sub>F\<^sub>M\<^sub>U fmu)   time)) \<and> (pre_calculate oValue   (env\<^sub>F\<^sub>M\<^sub>U fmu)   time))))) then
		(dummy0RANGE)
		else
		(undefined))))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e (
		if ((\<exists> (dummy0RANGE :: FMIValue)  . ((( ((((case (fmiValue\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e dummy0RANGE) of
		 ValueType.U_bool (fmiValue\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e dummy0RANGE) \<Rightarrow> (inv_bool (fmiValue\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e dummy0RANGE))
		  | ValueType.U_VDMReal (fmiValue\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e dummy0RANGE) \<Rightarrow> (inv_VDMReal (fmiValue\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e dummy0RANGE))
		 ))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e dummy0RANGE))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e dummy0RANGE)))) )) ))) \<longrightarrow> (\<comment>\<open>Transform a VDM `=` expression into an `eq_FMIValue` call\<close>
	(eq_FMIValue dummy0RANGE   (calculate oValue   (env\<^sub>F\<^sub>M\<^sub>U fmu)   time)) \<and> (pre_calculate oValue   (env\<^sub>F\<^sub>M\<^sub>U fmu)   time))))) then
		(dummy0RANGE)
		else
		(undefined)))))) )) ) then
			(
		if ((\<exists> (dummy0RANGE :: FMIValue)  . ((( ((((case (fmiValue\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e dummy0RANGE) of
		 ValueType.U_bool (fmiValue\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e dummy0RANGE) \<Rightarrow> (inv_bool (fmiValue\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e dummy0RANGE))
		  | ValueType.U_VDMReal (fmiValue\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e dummy0RANGE) \<Rightarrow> (inv_VDMReal (fmiValue\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e dummy0RANGE))
		 ))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e dummy0RANGE))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e dummy0RANGE)))) )) ))) \<longrightarrow> (\<comment>\<open>Transform a VDM `=` expression into an `eq_FMIValue` call\<close>
	(eq_FMIValue dummy0RANGE   (calculate oValue   (env\<^sub>F\<^sub>M\<^sub>U fmu)   time)) \<and> (pre_calculate oValue   (env\<^sub>F\<^sub>M\<^sub>U fmu)   time))))) then
		(dummy0RANGE)
		else
		(undefined))
		 else
			undefined
		)
		) 
		(
	\<lambda> (dummy0DOMAIN :: VDMNat)   (dummy0RANGE :: FMIValue) .
		(if (((inv_VDMNat dummy0DOMAIN)))  \<and>  (( ((((case (fmiValue\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e dummy0RANGE) of
		 ValueType.U_bool (fmiValue\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e dummy0RANGE) \<Rightarrow> (inv_bool (fmiValue\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e dummy0RANGE))
		  | ValueType.U_VDMReal (fmiValue\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e dummy0RANGE) \<Rightarrow> (inv_VDMReal (fmiValue\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e dummy0RANGE))
		 ))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e dummy0RANGE))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e dummy0RANGE)))) )) ))) \<and> (inv_bool (
		if ((\<exists> oValue \<in> ((dom (env\<^sub>F\<^sub>M\<^sub>U fmu)) \<inter> outputRef)  . ((oValue \<in> ((dom (env\<^sub>F\<^sub>M\<^sub>U fmu)) \<inter> outputRef)) \<and> (pre_calculate oValue   (env\<^sub>F\<^sub>M\<^sub>U fmu)   time)))) then
		((True::\<bool>))
		else
		(undefined))) then
			(
		if ((\<exists> oValue \<in> ((dom (env\<^sub>F\<^sub>M\<^sub>U fmu)) \<inter> outputRef)  . ((oValue \<in> ((dom (env\<^sub>F\<^sub>M\<^sub>U fmu)) \<inter> outputRef)) \<and> (pre_calculate oValue   (env\<^sub>F\<^sub>M\<^sub>U fmu)   time)))) then
		((True::\<bool>))
		else
		(undefined))
		 else
			undefined
		)
		))
		 else
			undefined
		)
		)"

	
	
\<comment>\<open>VDM source: calculate: (Ref * Environment * Time -> FMIValue)
	calculate(ref, env, time) ==
mk_FMIValue((env(ref).fmiValue), time)
	pre (ref in set (dom env))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 511:5\<close>

\<comment>\<open>VDM source: pre_calculate: (Ref * Environment * Time +> bool)
	pre_calculate(ref, env, time) ==
(ref in set (dom env))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 517:13\<close>
definition
	pre_calculate :: "Ref \<Rightarrow> Environment \<Rightarrow> Time \<Rightarrow> bool"
where
	"pre_calculate ref   env   time \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `pre_calculate` specification.\<close>
		((inv_Ref ref)  \<and>  (inv_Environment env)  \<and>  inv_Time time)  \<and> 
		\<comment>\<open>User defined body of pre_calculate.\<close>
		(ref \<in> (dom env))"


\<comment>\<open>VDM source: post_calculate: (Ref * Environment * Time * FMIValue +> bool)
	post_calculate(ref, env, time, RESULT) ==
null\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 511:5\<close>
definition
	post_calculate :: "Ref \<Rightarrow> Environment \<Rightarrow> Time \<Rightarrow> FMIValue \<Rightarrow> bool"
where
	"post_calculate ref   env   time   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_calculate` specification.\<close>
		((inv_Ref ref)  \<and>  (inv_Environment env)  \<and>  inv_Time time  \<and>  inv_FMIValue RESULT)"

definition
	calculate :: "Ref \<Rightarrow> Environment \<Rightarrow> Time \<Rightarrow> FMIValue"
where
	"calculate ref   env   time \<equiv> 
	\<comment>\<open>User defined body of calculate.\<close>
	\<lparr>fmiValue\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e = (fmiValue\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e (the((env ref)))), time\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e = time\<rparr>"

	
	
\<comment>\<open>VDM source: step_tm: (FMU * Real1 +> (FMU * Real1 * bool))
	step_tm(fmu, step) ==
let mk_(stepTaken, eventTriggered):(Real1 * bool) = (if (step >= (fmu.maxStep))
then mk_((fmu.maxStep), true)
else mk_(step, false)), newTime:Time = mk_Time((((fmu.time).r) + stepTaken), ((fmu.time).i)), updatedFMU:FMU = mu(fmu, time |-> newTime, env |-> updateOutputs(fmu, newTime), stepped |-> true) in mk_(updatedFMU, stepTaken, eventTriggered)
	pre (preStepT(fmu, step) and (pre_preStepT(fmu, step) and let mk_(stepTaken, eventTriggered):(Real1 * bool) = (if (step >= (fmu.maxStep))
then mk_((fmu.maxStep), true)
else mk_(step, false)), newTime:Time = mk_Time((((fmu.time).r) + stepTaken), ((fmu.time).i)) in pre_updateOutputs(fmu, newTime)))
	post (pre_postStepT((RESULT.#1), (RESULT.#2), (RESULT.#3), fmu, step) and postStepT((RESULT.#1), (RESULT.#2), (RESULT.#3), fmu, step))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 519:5\<close>

\<comment>\<open>VDM source: pre_step_tm: (FMU * Real1 +> bool)
	pre_step_tm(fmu, step) ==
(preStepT(fmu, step) and (pre_preStepT(fmu, step) and let mk_(stepTaken, eventTriggered):(Real1 * bool) = (if (step >= (fmu.maxStep))
then mk_((fmu.maxStep), true)
else mk_(step, false)), newTime:Time = mk_Time((((fmu.time).r) + stepTaken), ((fmu.time).i)) in pre_updateOutputs(fmu, newTime)))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 534:9\<close>
definition
	pre_step_tm :: "FMU \<Rightarrow> Real1 \<Rightarrow> bool"
where
	"pre_step_tm fmu   step \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `pre_step_tm` specification.\<close>
		(inv_FMU fmu  \<and>  (inv_Real1 step))  \<and> 
		\<comment>\<open>User defined body of pre_step_tm.\<close>
		((preStepT fmu   step) \<and> ((pre_preStepT fmu   step) \<and> (
		let 
(eventTriggered::bool) = (
		if ((step \<ge> (maxStep\<^sub>F\<^sub>M\<^sub>U fmu))) then
		(((maxStep\<^sub>F\<^sub>M\<^sub>U fmu) , (True::\<bool>)))
		else
		((step , (False::\<bool>))));
(stepTaken::Real1) = (
		if ((step \<ge> (maxStep\<^sub>F\<^sub>M\<^sub>U fmu))) then
		(((maxStep\<^sub>F\<^sub>M\<^sub>U fmu) , (True::\<bool>)))
		else
		((step , (False::\<bool>))))
		;
		
(newTime::Time) = \<lparr>r\<^sub>T\<^sub>i\<^sub>m\<^sub>e = ((r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U fmu)) + stepTaken), i\<^sub>T\<^sub>i\<^sub>m\<^sub>e = (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U fmu))\<rparr>
		in
			(if (
		(((inv_VDMReal (fst dummy0)))\<and>
		 (inv_bool (snd dummy0))
		))
	 \<and> 
	(inv_Time newTime) then
			(pre_updateOutputs fmu   newTime)
		 else
			undefined
		)
		)))"


\<comment>\<open>VDM source: post_step_tm: (FMU * Real1 * (FMU * Real1 * bool) +> bool)
	post_step_tm(fmu, step, RESULT) ==
(pre_postStepT((RESULT.#1), (RESULT.#2), (RESULT.#3), fmu, step) and postStepT((RESULT.#1), (RESULT.#2), (RESULT.#3), fmu, step))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 543:9\<close>
definition
	post_step_tm :: "FMU \<Rightarrow> Real1 \<Rightarrow> (FMU \<times> Real1 \<times> bool) \<Rightarrow> bool"
where
	"post_step_tm fmu   step   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `post_step_tm` specification.\<close>
		(inv_FMU fmu  \<and>  (inv_Real1 step)  \<and>  
		(inv_FMU (fst RESULT)\<and>
		 (inv_Real1 (fst (snd RESULT)))\<and>
		 (inv_bool (snd (snd RESULT)))
		))  \<and> 
		\<comment>\<open>User defined body of post_step_tm.\<close>
		((pre_postStepT (fst (RESULT))   (fst (snd (RESULT)))   (snd (snd (RESULT)))   fmu   step) \<and> (postStepT (fst (RESULT))   (fst (snd (RESULT)))   (snd (snd (RESULT)))   fmu   step))"

definition
	step_tm :: "FMU \<Rightarrow> Real1 \<Rightarrow> (FMU \<times> Real1 \<times> bool)"
where
	"step_tm fmu   step \<equiv> 
	\<comment>\<open>User defined body of step_tm.\<close>
	(
		let 
(eventTriggered::bool) = (
		if ((step \<ge> (maxStep\<^sub>F\<^sub>M\<^sub>U fmu))) then
		(((maxStep\<^sub>F\<^sub>M\<^sub>U fmu) , (True::\<bool>)))
		else
		((step , (False::\<bool>))));
(stepTaken::Real1) = (
		if ((step \<ge> (maxStep\<^sub>F\<^sub>M\<^sub>U fmu))) then
		(((maxStep\<^sub>F\<^sub>M\<^sub>U fmu) , (True::\<bool>)))
		else
		((step , (False::\<bool>))))
		;
		
(newTime::Time) = \<lparr>r\<^sub>T\<^sub>i\<^sub>m\<^sub>e = ((r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U fmu)) + stepTaken), i\<^sub>T\<^sub>i\<^sub>m\<^sub>e = (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U fmu))\<rparr>
		;
		
(updatedFMU::FMU) = (fmu)\<lparr>time\<^sub>F\<^sub>M\<^sub>U := newTime, env\<^sub>F\<^sub>M\<^sub>U := (updateOutputs fmu   newTime), stepped\<^sub>F\<^sub>M\<^sub>U := (True::\<bool>)\<rparr>
		in
			(if (
		(((inv_VDMReal (fst dummy0)))\<and>
		 (inv_bool (snd dummy0))
		))
	 \<and> 
	(inv_Time newTime)
	 \<and> 
	(inv_FMU updatedFMU) then
			(updatedFMU , stepTaken , eventTriggered)
		 else
			undefined
		)
		)"

	
	
\<comment>\<open>VDM source: preStepE: (FMU -> bool)
	preStepE(fmu) ==
((fmu.mode) = <EVENT>)
	pre true\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 546:5\<close>

\<comment>\<open>VDM source: pre_preStepE: (FMU +> bool)
	pre_preStepE(fmu) ==
true\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 549:9\<close>
definition
	pre_preStepE :: "FMU \<Rightarrow> bool"
where
	"pre_preStepE fmu \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `pre_preStepE` specification.\<close>
		(inv_FMU fmu)  \<and> 
		\<comment>\<open>User defined body of pre_preStepE.\<close>
		(True::\<bool>)"


\<comment>\<open>VDM source: post_preStepE: (FMU * bool +> bool)
	post_preStepE(fmu, RESULT) ==
null\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 546:5\<close>
definition
	post_preStepE :: "FMU \<Rightarrow> bool \<Rightarrow> bool"
where
	"post_preStepE fmu   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_preStepE` specification.\<close>
		(inv_FMU fmu  \<and>  (inv_bool RESULT))"

definition
	preStepE :: "FMU \<Rightarrow> bool"
where
	"preStepE fmu \<equiv> 
	\<comment>\<open>User defined body of preStepE.\<close>
	((mode\<^sub>F\<^sub>M\<^sub>U fmu) = FMUMode.U_EVENT )"

	
	
\<comment>\<open>VDM source: postStepE: (FMU * FMU * bool -> bool)
	postStepE(fmu, oldFMU, -) ==
(((fmu.mode) = <EVENT>) and ((((fmu.time).i) = (((oldFMU.time).i) + 1)) and ((((fmu.time).r) = ((oldFMU.time).r)) and ((fmu.activeClocks) = {}))))
	pre true\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 551:5\<close>

\<comment>\<open>VDM source: pre_postStepE: (FMU * FMU * bool +> bool)
	pre_postStepE(fmu, oldFMU, -) ==
true\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 557:9\<close>
definition
	pre_postStepE :: "FMU \<Rightarrow> FMU \<Rightarrow> bool \<Rightarrow> bool"
where
	"pre_postStepE fmu   oldFMU   dummy0_ignore \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `pre_postStepE` specification.\<close>
		(inv_FMU fmu  \<and>  inv_FMU oldFMU  \<and>  (inv_bool dummy0_ignore))  \<and> 
		\<comment>\<open>User defined body of pre_postStepE.\<close>
		(True::\<bool>)"


\<comment>\<open>VDM source: post_postStepE: (FMU * FMU * bool * bool +> bool)
	post_postStepE(fmu, oldFMU, -, RESULT) ==
null\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 551:5\<close>
definition
	post_postStepE :: "FMU \<Rightarrow> FMU \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool"
where
	"post_postStepE fmu   oldFMU   dummy0_ignore   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_postStepE` specification.\<close>
		(inv_FMU fmu  \<and>  inv_FMU oldFMU  \<and>  (inv_bool dummy0_ignore)  \<and>  (inv_bool RESULT))"

definition
	postStepE :: "FMU \<Rightarrow> FMU \<Rightarrow> bool \<Rightarrow> bool"
where
	"postStepE fmu   oldFMU   dummy0_ignore \<equiv> 
	\<comment>\<open>User defined body of postStepE.\<close>
	(((mode\<^sub>F\<^sub>M\<^sub>U fmu) = FMUMode.U_EVENT ) \<and> (((i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U fmu)) = ((i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U oldFMU)) + (1::VDMNat1))) \<and> (((r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U fmu)) = (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U oldFMU))) \<and> ((activeClocks\<^sub>F\<^sub>M\<^sub>U fmu) = {}))))"

	
	
\<comment>\<open>VDM source: step_e: (FMU +> (FMU * bool))
	step_e(fmu) ==
let updatedFMU:FMU = mu(fmu, time |-> mk_Time(((fmu.time).r), (((fmu.time).i) + 1)), activeClocks |-> {}) in mk_(updatedFMU, false)
	pre (preStepE(fmu) and pre_preStepE(fmu))
	post (pre_postStepE((RESULT.#1), fmu, (RESULT.#2)) and postStepE((RESULT.#1), fmu, (RESULT.#2)))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 559:5\<close>

\<comment>\<open>VDM source: pre_step_e: (FMU +> bool)
	pre_step_e(fmu) ==
(preStepE(fmu) and pre_preStepE(fmu))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 568:23\<close>
definition
	pre_step_e :: "FMU \<Rightarrow> bool"
where
	"pre_step_e fmu \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `pre_step_e` specification.\<close>
		(inv_FMU fmu)  \<and> 
		\<comment>\<open>User defined body of pre_step_e.\<close>
		((preStepE fmu) \<and> (pre_preStepE fmu))"


\<comment>\<open>VDM source: post_step_e: (FMU * (FMU * bool) +> bool)
	post_step_e(fmu, RESULT) ==
(pre_postStepE((RESULT.#1), fmu, (RESULT.#2)) and postStepE((RESULT.#1), fmu, (RESULT.#2)))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 569:51\<close>
definition
	post_step_e :: "FMU \<Rightarrow> (FMU \<times> bool) \<Rightarrow> bool"
where
	"post_step_e fmu   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `post_step_e` specification.\<close>
		(inv_FMU fmu  \<and>  
		(inv_FMU (fst RESULT)\<and>
		 (inv_bool (snd RESULT))
		))  \<and> 
		\<comment>\<open>User defined body of post_step_e.\<close>
		((pre_postStepE (fst (RESULT))   fmu   (snd (RESULT))) \<and> (postStepE (fst (RESULT))   fmu   (snd (RESULT))))"

definition
	step_e :: "FMU \<Rightarrow> (FMU \<times> bool)"
where
	"step_e fmu \<equiv> 
	\<comment>\<open>User defined body of step_e.\<close>
	(
		let 
(updatedFMU::FMU) = (fmu)\<lparr>time\<^sub>F\<^sub>M\<^sub>U := \<lparr>r\<^sub>T\<^sub>i\<^sub>m\<^sub>e = (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U fmu)), i\<^sub>T\<^sub>i\<^sub>m\<^sub>e = ((i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U fmu)) + (1::VDMNat1))\<rparr>, activeClocks\<^sub>F\<^sub>M\<^sub>U := {}\<rparr>
		in
			(if (inv_FMU updatedFMU) then
			(updatedFMU , (False::\<bool>))
		 else
			undefined
		)
		)"

	
	
\<comment>\<open>VDM source: next_tm: (FMU * Ref +> RealNaN)
	next_tm(fmu, ref) ==
not yet specified
	pre (exists [v in set (fmu.clocks)] & (((v.ref) = ref) and (((v.type) = <input>) and ((v.interval) in set {<tunable>, <changing>, <countdown>}))))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 575:5\<close>

\<comment>\<open>VDM source: pre_next_tm: (FMU * Ref +> bool)
	pre_next_tm(fmu, ref) ==
(exists [v in set (fmu.clocks)] & (((v.ref) = ref) and (((v.type) = <input>) and ((v.interval) in set {<tunable>, <changing>, <countdown>}))))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 578:9\<close>
definition
	pre_next_tm :: "FMU \<Rightarrow> Ref \<Rightarrow> bool"
where
	"pre_next_tm fmu   ref \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `pre_next_tm` specification.\<close>
		(inv_FMU fmu  \<and>  (inv_Ref ref))  \<and> 
		\<comment>\<open>User defined body of pre_next_tm.\<close>
		(\<exists> v \<in> (clocks\<^sub>F\<^sub>M\<^sub>U fmu)  . (((ref\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k v) = ref) \<and> (((type\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k v) = Causality.U_input ) \<and> ((interval\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k v) \<in> {Interval.U_tunable  , Interval.U_changing  , Interval.U_countdown }))))"


\<comment>\<open>VDM source: post_next_tm: (FMU * Ref * RealNaN +> bool)
	post_next_tm(fmu, ref, RESULT) ==
null\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 575:5\<close>
definition
	post_next_tm :: "FMU \<Rightarrow> Ref \<Rightarrow> RealNaN \<Rightarrow> bool"
where
	"post_next_tm fmu   ref   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_next_tm` specification.\<close>
		(inv_FMU fmu  \<and>  (inv_Ref ref)  \<and>  (inv_RealNaN RESULT))"

definition
	next_tm :: "FMU \<Rightarrow> Ref \<Rightarrow> RealNaN"
where
	"next_tm fmu   ref \<equiv> 
	\<comment>\<open>User defined body of next_tm.\<close>
	undefined"

	
	
\<comment>\<open>VDM source: createFMURefs: (FMU * set of (Ref) -> set of (FMURef))
	createFMURefs(fmu, clocks) ==
{mk_FMURef((fmu.name), clock) | clock in set clocks}
	pre true
	post ((card RESULT) = (card clocks))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 582:5\<close>

\<comment>\<open>VDM source: pre_createFMURefs: (FMU * set of (Ref) +> bool)
	pre_createFMURefs(fmu, clocks) ==
true\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 585:9\<close>
definition
	pre_createFMURefs :: "FMU \<Rightarrow> Ref VDMSet \<Rightarrow> bool"
where
	"pre_createFMURefs fmu   clocks \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `pre_createFMURefs` specification.\<close>
		(inv_FMU fmu  \<and>  (inv_VDMSet' (inv_Ref) clocks))  \<and> 
		\<comment>\<open>User defined body of pre_createFMURefs.\<close>
		(True::\<bool>)"


\<comment>\<open>VDM source: post_createFMURefs: (FMU * set of (Ref) * set of (FMURef) +> bool)
	post_createFMURefs(fmu, clocks, RESULT) ==
((card RESULT) = (card clocks))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 586:22\<close>
definition
	post_createFMURefs :: "FMU \<Rightarrow> Ref VDMSet \<Rightarrow> FMURef VDMSet \<Rightarrow> bool"
where
	"post_createFMURefs fmu   clocks   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `post_createFMURefs` specification.\<close>
		(inv_FMU fmu  \<and>  (inv_VDMSet' (inv_Ref) clocks)  \<and>  (inv_VDMSet' inv_FMURef  RESULT))  \<and> 
		\<comment>\<open>User defined body of post_createFMURefs.\<close>
		((vdm_card RESULT) = (vdm_card clocks))"

definition
	createFMURefs :: "FMU \<Rightarrow> Ref VDMSet \<Rightarrow> FMURef VDMSet"
where
	"createFMURefs fmu   clocks \<equiv> 
	\<comment>\<open>User defined body of createFMURefs.\<close>
	{ \<lparr>name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f = (name\<^sub>F\<^sub>M\<^sub>U fmu), ref\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f = clock\<rparr> | clock .  ((clock \<in>clocks))  }"

	
	
\<comment>\<open>VDM source: ClocksImporter = compose ClocksImporter of activeClocks:set of (FMURef), readyClocks:set of (FMURef), inactiveClocks:set of (FMURef), relevantOutputClocks:set of (FMURef), relevantInputClocks:set of (FMURef) end
	inv mk_ClocksImporter(activeClocks, readyClocks, inactiveClocks, relevantInputClocks, relevantOutputClocks) == (((activeClocks inter readyClocks) = {}) and (((inactiveClocks inter activeClocks) = {}) and (((inactiveClocks inter readyClocks) = {}) and ((relevantInputClocks inter relevantOutputClocks) = {}))))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 592:5\<close>
record ClocksImporter = 
	activeClocks\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k\<^sub>s\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r :: "FMURef VDMSet"
		 
		 readyClocks\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k\<^sub>s\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r :: "FMURef VDMSet"
		 
		 inactiveClocks\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k\<^sub>s\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r :: "FMURef VDMSet"
		 
		 relevantOutputClocks\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k\<^sub>s\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r :: "FMURef VDMSet"
		 
		 relevantInputClocks\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k\<^sub>s\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r :: "FMURef VDMSet"
	

\<comment>\<open>VDM source: inv_ClocksImporter: (ClocksImporter +> bool)
	inv_ClocksImporter(mk_ClocksImporter(activeClocks, readyClocks, inactiveClocks, relevantInputClocks, relevantOutputClocks)) ==
(((activeClocks inter readyClocks) = {}) and (((inactiveClocks inter activeClocks) = {}) and (((inactiveClocks inter readyClocks) = {}) and ((relevantInputClocks inter relevantOutputClocks) = {}))))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 598:9\<close>
definition
	inv_ClocksImporter :: "ClocksImporter \<Rightarrow> bool"
where
	"inv_ClocksImporter dummy0 \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `inv_ClocksImporter` specification.\<close>
		( (((inv_VDMSet' inv_FMURef  (activeClocks\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k\<^sub>s\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r dummy0))) \<and> 
		 ((inv_VDMSet' inv_FMURef  (readyClocks\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k\<^sub>s\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r dummy0))) \<and> 
		 ((inv_VDMSet' inv_FMURef  (inactiveClocks\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k\<^sub>s\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r dummy0))) \<and> 
		 ((inv_VDMSet' inv_FMURef  (relevantOutputClocks\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k\<^sub>s\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r dummy0))) \<and> 
		 ((inv_VDMSet' inv_FMURef  (relevantInputClocks\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k\<^sub>s\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r dummy0))) ))  \<and> 
		\<comment>\<open>Implicit pattern context conversion\<close>
		(let activeClocks = (activeClocks\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k\<^sub>s\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r dummy0); readyClocks = (readyClocks\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k\<^sub>s\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r dummy0); inactiveClocks = (inactiveClocks\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k\<^sub>s\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r dummy0); relevantInputClocks = (relevantOutputClocks\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k\<^sub>s\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r dummy0); relevantOutputClocks = (relevantInputClocks\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k\<^sub>s\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r dummy0) in 
		\<comment>\<open>User defined body of inv_ClocksImporter.\<close>
		(((activeClocks \<inter> readyClocks) = {}) \<and> (((inactiveClocks \<inter> activeClocks) = {}) \<and> (((inactiveClocks \<inter> readyClocks) = {}) \<and> ((relevantInputClocks \<inter> relevantOutputClocks) = {})))))"

		
lemmas inv_ClocksImporter_defs = inv_ClocksImporter_def inv_FMURef_def inv_Name_def inv_Ref_def inv_VDMChar_def inv_VDMNat_def inv_VDMSeq1'_def inv_VDMSeq1'_defs inv_VDMSet'_def inv_VDMSet'_defs 


	
	
\<comment>\<open>VDM source: ClocksByType: (FMU * Causality -> set of (Ref))
	ClocksByType(fmu, type) ==
{(clock.ref) | clock in set (fmu.clocks) & ((clock.type) = type)}
	pre true\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 616:5\<close>

\<comment>\<open>VDM source: pre_ClocksByType: (FMU * Causality +> bool)
	pre_ClocksByType(fmu, type) ==
true\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 619:9\<close>
definition
	pre_ClocksByType :: "FMU \<Rightarrow> Causality \<Rightarrow> bool"
where
	"pre_ClocksByType fmu   type \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `pre_ClocksByType` specification.\<close>
		(inv_FMU fmu  \<and>  (inv_Causality type))  \<and> 
		\<comment>\<open>User defined body of pre_ClocksByType.\<close>
		(
		\<comment>\<open>Implicit union type parameters projection\<close>
		())"


\<comment>\<open>VDM source: post_ClocksByType: (FMU * Causality * set of (Ref) +> bool)
	post_ClocksByType(fmu, type, RESULT) ==
null\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 616:5\<close>
definition
	post_ClocksByType :: "FMU \<Rightarrow> Causality \<Rightarrow> Ref VDMSet \<Rightarrow> bool"
where
	"post_ClocksByType fmu   type   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_ClocksByType` specification.\<close>
		(inv_FMU fmu  \<and>  (inv_Causality type)  \<and>  (inv_VDMSet' (inv_Ref) RESULT))"

definition
	ClocksByType :: "FMU \<Rightarrow> Causality \<Rightarrow> Ref VDMSet"
where
	"ClocksByType fmu   type \<equiv> 
	\<comment>\<open>User defined body of ClocksByType.\<close>
	(
	\<comment>\<open>Implicit union type parameters projection\<close>
	())"

	
	
\<comment>\<open>VDM source: Importer = compose Importer of scenario:Scenario, schedule:map (Name) to (Real1), activeClocks:set of (FMURef), readyClocks:set of (FMURef), inactiveClocks:set of (FMURef), fmusWithEvent:set of (Name), relevantOutputClocks:set of (FMURef), relevantInputClocks:set of (FMURef), activeEquations:set of (FMURef), calculatedEquations:set of (FMURef), readyEquations:set of (FMURef), time:Time, endtime:Time, stepSize:Real1, valueMap:map (FMURef) to (FMIValue) end
	inv imp == let fmus:map (Name) to (FMU) = ((imp.scenario).fmus) in let inputclocks:set of (FMURef) = (dunion {createFMURefs(fmu, ClocksByType(fmu, <input>)) | fmu in set (rng fmus) & (pre_ClocksByType(fmu, <input>) and pre_createFMURefs(fmu, ClocksByType(fmu, <input>)))}) in let outputclocks:set of (FMURef) = (dunion {createFMURefs(fmu, ClocksByType(fmu, <output>)) | fmu in set (rng fmus) & (pre_ClocksByType(fmu, <output>) and pre_createFMURefs(fmu, ClocksByType(fmu, <output>)))}) in let clocks:set of (FMURef) = (inputclocks union outputclocks) in (((card ((imp.activeClocks) union (imp.inactiveClocks))) = (card clocks)) and ((((imp.activeClocks) inter (imp.inactiveClocks)) = {}) and ((((imp.activeClocks) inter (imp.readyClocks)) = {}) and (((imp.activeClocks) = (dunion {createFMURefs(fmu, (fmu.activeClocks)) | fmu in set (rng fmus)})) and (((imp.fmusWithEvent) subset (dom fmus)) and (((imp.relevantInputClocks) subset inputclocks) and (((imp.relevantOutputClocks) subset outputclocks) and ((((imp.relevantInputClocks) inter (imp.relevantOutputClocks)) = {}) and (((imp.endtime) >= (imp.time)) and ((((imp.activeEquations) inter (imp.readyEquations)) = {}) and (((imp.readyEquations) inter (imp.calculatedEquations)) = {})))))))))))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 628:5\<close>
record Importer = 
	scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r :: "Scenario"
		 
		 schedule\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r :: "(Name \<rightharpoonup> Real1)"
		 
		 activeClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r :: "FMURef VDMSet"
		 
		 readyClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r :: "FMURef VDMSet"
		 
		 inactiveClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r :: "FMURef VDMSet"
		 
		 fmusWithEvent\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r :: "Name VDMSet"
		 
		 relevantOutputClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r :: "FMURef VDMSet"
		 
		 relevantInputClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r :: "FMURef VDMSet"
		 
		 activeEquations\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r :: "FMURef VDMSet"
		 
		 calculatedEquations\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r :: "FMURef VDMSet"
		 
		 readyEquations\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r :: "FMURef VDMSet"
		 
		 time\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r :: "Time"
		 
		 endtime\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r :: "Time"
		 
		 stepSize\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r :: "Real1"
		 
		 valueMap\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r :: "(FMURef \<rightharpoonup> FMIValue)"
	

\<comment>\<open>VDM source: inv_Importer: (Importer +> bool)
	inv_Importer(imp) ==
let fmus:map (Name) to (FMU) = ((imp.scenario).fmus) in let inputclocks:set of (FMURef) = (dunion {createFMURefs(fmu, ClocksByType(fmu, <input>)) | fmu in set (rng fmus) & (pre_ClocksByType(fmu, <input>) and pre_createFMURefs(fmu, ClocksByType(fmu, <input>)))}) in let outputclocks:set of (FMURef) = (dunion {createFMURefs(fmu, ClocksByType(fmu, <output>)) | fmu in set (rng fmus) & (pre_ClocksByType(fmu, <output>) and pre_createFMURefs(fmu, ClocksByType(fmu, <output>)))}) in let clocks:set of (FMURef) = (inputclocks union outputclocks) in (((card ((imp.activeClocks) union (imp.inactiveClocks))) = (card clocks)) and ((((imp.activeClocks) inter (imp.inactiveClocks)) = {}) and ((((imp.activeClocks) inter (imp.readyClocks)) = {}) and (((imp.activeClocks) = (dunion {createFMURefs(fmu, (fmu.activeClocks)) | fmu in set (rng fmus)})) and (((imp.fmusWithEvent) subset (dom fmus)) and (((imp.relevantInputClocks) subset inputclocks) and (((imp.relevantOutputClocks) subset outputclocks) and ((((imp.relevantInputClocks) inter (imp.relevantOutputClocks)) = {}) and (((imp.endtime) >= (imp.time)) and ((((imp.activeEquations) inter (imp.readyEquations)) = {}) and (((imp.readyEquations) inter (imp.calculatedEquations)) = {})))))))))))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 644:9\<close>
definition
	inv_Importer :: "Importer \<Rightarrow> bool"
where
	"inv_Importer imp \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `inv_Importer` specification.\<close>
		( ((inv_Scenario (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r imp)) \<and> 
		 ((inv_Map (inv_Name) (inv_Real1) (schedule\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r imp))) \<and> 
		 ((inv_VDMSet' inv_FMURef  (activeClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r imp))) \<and> 
		 ((inv_VDMSet' inv_FMURef  (readyClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r imp))) \<and> 
		 ((inv_VDMSet' inv_FMURef  (inactiveClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r imp))) \<and> 
		 ((inv_VDMSet' (inv_Name) (fmusWithEvent\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r imp))) \<and> 
		 ((inv_VDMSet' inv_FMURef  (relevantOutputClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r imp))) \<and> 
		 ((inv_VDMSet' inv_FMURef  (relevantInputClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r imp))) \<and> 
		 ((inv_VDMSet' inv_FMURef  (activeEquations\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r imp))) \<and> 
		 ((inv_VDMSet' inv_FMURef  (calculatedEquations\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r imp))) \<and> 
		 ((inv_VDMSet' inv_FMURef  (readyEquations\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r imp))) \<and> 
		 (inv_Time (time\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r imp)) \<and> 
		 (inv_Time (endtime\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r imp)) \<and> 
		 ((inv_Real1 (stepSize\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r imp))) \<and> 
		 ((inv_Map inv_FMURef  inv_FMIValue  (valueMap\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r imp))) ))  \<and> 
		\<comment>\<open>User defined body of inv_Importer.\<close>
		(
		let 
(fmus::(Name \<rightharpoonup> FMU)) = (fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r imp))
		in
			(if ((inv_Map ((inv_VDMSeq1' (inv_VDMChar))) inv_FMU  fmus)) then
			(
		let 
(inputclocks::FMURef VDMSet) = (\<Union> { (createFMURefs fmu   (ClocksByType fmu   Causality.U_input )) | fmu .  ((fmu \<in>(rng fmus)))  \<and> ((pre_ClocksByType fmu   Causality.U_input ) \<and> (pre_createFMURefs fmu   (ClocksByType fmu   Causality.U_input ))) })
		in
			(if ((inv_VDMSet' inv_FMURef  inputclocks)) then
			(
		let 
(outputclocks::FMURef VDMSet) = (\<Union> { (createFMURefs fmu   (ClocksByType fmu   Causality.U_output )) | fmu .  ((fmu \<in>(rng fmus)))  \<and> ((pre_ClocksByType fmu   Causality.U_output ) \<and> (pre_createFMURefs fmu   (ClocksByType fmu   Causality.U_output ))) })
		in
			(if ((inv_VDMSet' inv_FMURef  outputclocks)) then
			(
		let 
(clocks::FMURef VDMSet) = (inputclocks \<union> outputclocks)
		in
			(if ((inv_VDMSet' inv_FMURef  clocks)) then
			(((vdm_card ((activeClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r imp) \<union> (inactiveClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r imp))) = (vdm_card clocks)) \<and> ((((activeClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r imp) \<inter> (inactiveClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r imp)) = {}) \<and> ((((activeClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r imp) \<inter> (readyClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r imp)) = {}) \<and> (((activeClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r imp) = (\<Union> { (createFMURefs fmu   (activeClocks\<^sub>F\<^sub>M\<^sub>U fmu)) | fmu .  ((fmu \<in>(rng fmus)))  })) \<and> (((fmusWithEvent\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r imp) \<subseteq> (dom fmus)) \<and> (((relevantInputClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r imp) \<subseteq> inputclocks) \<and> (((relevantOutputClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r imp) \<subseteq> outputclocks) \<and> ((((relevantInputClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r imp) \<inter> (relevantOutputClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r imp)) = {}) \<and> (\<comment>\<open>Transform a VDM `>` expression into a reversed `ord_Time` call\<close>
	(ord_Time (time\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r imp)   (endtime\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r imp)) \<or> 
	\<comment>\<open>Transform a VDM `=` expression into an `eq_Time` call\<close>
	(eq_Time (endtime\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r imp)   (time\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r imp)) \<and> ((((activeEquations\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r imp) \<inter> (readyEquations\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r imp)) = {}) \<and> (((readyEquations\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r imp) \<inter> (calculatedEquations\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r imp)) = {})))))))))))
		 else
			undefined
		)
		)
		 else
			undefined
		)
		)
		 else
			undefined
		)
		)
		 else
			undefined
		)
		)"
 
lemmas inv_Importer_defs = inv_Causality_def inv_Clock_def inv_Connections_def inv_Contract_def inv_Environment_def inv_Equation_def inv_FMIValue_def inv_FMU_def inv_FMUMode_def inv_FMURef_def inv_IOLeo_def inv_Importer_def inv_Interval_def inv_Lambda_def inv_Map_def inv_Map_defs inv_Name_def inv_PortType_def inv_Real1_def inv_Ref_def inv_Scenario_def inv_ScenarioConnections_def inv_Time_def inv_TimeBasedClock_def inv_True_def inv_VDMChar_def inv_VDMNat_def inv_VDMReal_def inv_VDMSeq1'_def inv_VDMSeq1'_defs inv_VDMSet'_def inv_VDMSet'_defs inv_VDMSet1'_def inv_VDMSet1'_defs inv_ValueType_def inv_Variable_def inv_bool_def 


	
	
\<comment>\<open>VDM source: updateEnvironmentClock: (Importer * FMU * Ref * bool -> Importer)
	updateEnvironmentClock(I, fmu, clock, val) ==
let fmuref:FMURef = mk_FMURef((fmu.name), clock), activatedVariables:set of (FMURef) = createFMURefs(fmu, (dunion {(c.equations) | c in set (fmu.clocks) & (clock = (c.ref))})) in mu(I, scenario |-> mu((I.scenario), fmus |-> (((I.scenario).fmus) ++ {(fmu.name) |-> fmu})), activeClocks |-> (if val
then ((I.activeClocks) union {fmuref})
else ((I.activeClocks) \ {fmuref})), readyClocks |-> (if val
then ((I.readyClocks) \ {fmuref})
else (I.readyClocks)), inactiveClocks |-> (if val
then ((I.inactiveClocks) \ {fmuref})
else ((I.inactiveClocks) union {fmuref})), activeEquations |-> (if val
then ((I.activeEquations) union activatedVariables)
else ((I.activeEquations) \ activatedVariables)), readyEquations |-> (if val
then ((I.readyEquations) \ activatedVariables)
else (I.readyEquations)))
	pre true
	post let fmuRef:FMURef = mk_FMURef((fmu.name), clock) in (pre_createFMURefs(fmu, (dunion {(c.equations) | c in set (fmu.clocks) & (clock = (c.ref))})) and ((val => (((I.activeClocks) subset (RESULT.activeClocks)) and (((RESULT.readyClocks) psubset (I.readyClocks)) and (((RESULT.inactiveClocks) psubset (I.inactiveClocks)) and (fmuRef in set (RESULT.activeClocks)))))) and ((not val) => (fmuRef in set (RESULT.inactiveClocks)))))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 684:5\<close>

\<comment>\<open>VDM source: pre_updateEnvironmentClock: (Importer * FMU * Ref * bool +> bool)
	pre_updateEnvironmentClock(I, fmu, clock, val) ==
true\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 696:9\<close>
definition
	pre_updateEnvironmentClock :: "Importer \<Rightarrow> FMU \<Rightarrow> Ref \<Rightarrow> bool \<Rightarrow> bool"
where
	"pre_updateEnvironmentClock I   fmu   clock   val \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `pre_updateEnvironmentClock` specification.\<close>
		(inv_Importer I  \<and>  inv_FMU fmu  \<and>  (inv_Ref clock)  \<and>  (inv_bool val))  \<and> 
		\<comment>\<open>User defined body of pre_updateEnvironmentClock.\<close>
		(True::\<bool>)"


\<comment>\<open>VDM source: post_updateEnvironmentClock: (Importer * FMU * Ref * bool * Importer +> bool)
	post_updateEnvironmentClock(I, fmu, clock, val, RESULT) ==
let fmuRef:FMURef = mk_FMURef((fmu.name), clock) in (pre_createFMURefs(fmu, (dunion {(c.equations) | c in set (fmu.clocks) & (clock = (c.ref))})) and ((val => (((I.activeClocks) subset (RESULT.activeClocks)) and (((RESULT.readyClocks) psubset (I.readyClocks)) and (((RESULT.inactiveClocks) psubset (I.inactiveClocks)) and (fmuRef in set (RESULT.activeClocks)))))) and ((not val) => (fmuRef in set (RESULT.inactiveClocks)))))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 697:10\<close>
definition
	post_updateEnvironmentClock :: "Importer \<Rightarrow> FMU \<Rightarrow> Ref \<Rightarrow> bool \<Rightarrow> Importer \<Rightarrow> bool"
where
	"post_updateEnvironmentClock I   fmu   clock   val   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `post_updateEnvironmentClock` specification.\<close>
		(inv_Importer I  \<and>  inv_FMU fmu  \<and>  (inv_Ref clock)  \<and>  (inv_bool val)  \<and>  inv_Importer RESULT)  \<and> 
		\<comment>\<open>User defined body of post_updateEnvironmentClock.\<close>
		(
		let 
(fmuRef::FMURef) = \<lparr>name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f = (name\<^sub>F\<^sub>M\<^sub>U fmu), ref\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f = clock\<rparr>
		in
			(if (inv_FMURef fmuRef) then
			((pre_createFMURefs fmu   (\<Union> { (equations\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k c) | c .  ((c \<in>(clocks\<^sub>F\<^sub>M\<^sub>U fmu)))  \<and> (clock = (ref\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k c)) })) \<and> ((val \<longrightarrow> (((activeClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I) \<subseteq> (activeClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r RESULT)) \<and> (((readyClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r RESULT) \<subset> (readyClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) \<and> (((inactiveClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r RESULT) \<subset> (inactiveClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) \<and> (fmuRef \<in> (activeClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r RESULT)))))) \<and> ((\<not> val) \<longrightarrow> (fmuRef \<in> (inactiveClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r RESULT)))))
		 else
			undefined
		)
		)"

definition
	updateEnvironmentClock :: "Importer \<Rightarrow> FMU \<Rightarrow> Ref \<Rightarrow> bool \<Rightarrow> Importer"
where
	"updateEnvironmentClock I   fmu   clock   val \<equiv> 
	\<comment>\<open>User defined body of updateEnvironmentClock.\<close>
	(
		let 
(fmuref::FMURef) = \<lparr>name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f = (name\<^sub>F\<^sub>M\<^sub>U fmu), ref\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f = clock\<rparr>
		;
		
(activatedVariables::FMURef VDMSet) = (createFMURefs fmu   (\<Union> { (equations\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k c) | c .  ((c \<in>(clocks\<^sub>F\<^sub>M\<^sub>U fmu)))  \<and> (clock = (ref\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k c)) }))
		in
			(if (inv_FMURef fmuref)
	 \<and> 
	((inv_VDMSet' inv_FMURef  activatedVariables)) then
			(I)\<lparr>scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r := ((scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I))\<lparr>fmus\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r := ((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) \<dagger> [(name\<^sub>F\<^sub>M\<^sub>U fmu)\<mapsto>fmu])\<rparr>, activeClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r := (
		if (val) then
		(((activeClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I) \<union> {fmuref}))
		else
		(((activeClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I) - {fmuref}))), readyClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r := (
		if (val) then
		(((readyClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I) - {fmuref}))
		else
		((readyClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I))), inactiveClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r := (
		if (val) then
		(((inactiveClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I) - {fmuref}))
		else
		(((inactiveClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I) \<union> {fmuref}))), activeEquations\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r := (
		if (val) then
		(((activeEquations\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I) \<union> activatedVariables))
		else
		(((activeEquations\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I) - activatedVariables))), readyEquations\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r := (
		if (val) then
		(((readyEquations\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I) - activatedVariables))
		else
		((readyEquations\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)))\<rparr>
		 else
			undefined
		)
		)"

	
	
\<comment>\<open>VDM source: sameSetOfFMUs: (set of (FMU) * set of (FMU) -> bool)
	sameSetOfFMUs(fmus1, fmus2) ==
(((card fmus1) = (card fmus2)) and ({(m.name) | m in set fmus1} = {(m.name) | m in set fmus2}))
	pre true\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 711:5\<close>

\<comment>\<open>VDM source: pre_sameSetOfFMUs: (set of (FMU) * set of (FMU) +> bool)
	pre_sameSetOfFMUs(fmus1, fmus2) ==
true\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 716:13\<close>
definition
	pre_sameSetOfFMUs :: "FMU VDMSet \<Rightarrow> FMU VDMSet \<Rightarrow> bool"
where
	"pre_sameSetOfFMUs fmus1   fmus2 \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `pre_sameSetOfFMUs` specification.\<close>
		((inv_VDMSet' inv_FMU  fmus1)  \<and>  (inv_VDMSet' inv_FMU  fmus2))  \<and> 
		\<comment>\<open>User defined body of pre_sameSetOfFMUs.\<close>
		(True::\<bool>)"


\<comment>\<open>VDM source: post_sameSetOfFMUs: (set of (FMU) * set of (FMU) * bool +> bool)
	post_sameSetOfFMUs(fmus1, fmus2, RESULT) ==
null\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 711:5\<close>
definition
	post_sameSetOfFMUs :: "FMU VDMSet \<Rightarrow> FMU VDMSet \<Rightarrow> bool \<Rightarrow> bool"
where
	"post_sameSetOfFMUs fmus1   fmus2   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_sameSetOfFMUs` specification.\<close>
		((inv_VDMSet' inv_FMU  fmus1)  \<and>  (inv_VDMSet' inv_FMU  fmus2)  \<and>  (inv_bool RESULT))"

definition
	sameSetOfFMUs :: "FMU VDMSet \<Rightarrow> FMU VDMSet \<Rightarrow> bool"
where
	"sameSetOfFMUs fmus1   fmus2 \<equiv> 
	\<comment>\<open>User defined body of sameSetOfFMUs.\<close>
	(((vdm_card fmus1) = (vdm_card fmus2)) \<and> ({ (name\<^sub>F\<^sub>M\<^sub>U m) | m .  ((m \<in>fmus1))  } = { (name\<^sub>F\<^sub>M\<^sub>U m) | m .  ((m \<in>fmus2))  }))"

	
	
\<comment>\<open>VDM source: fmusNotAffected: (set of (FMU) * set of (FMU) -> bool)
	fmusNotAffected(oldFMUs, newFMUs) ==
(oldFMUs = newFMUs)
	pre (sameSetOfFMUs(oldFMUs, newFMUs) and pre_sameSetOfFMUs(oldFMUs, newFMUs))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 718:5\<close>

\<comment>\<open>VDM source: pre_fmusNotAffected: (set of (FMU) * set of (FMU) +> bool)
	pre_fmusNotAffected(oldFMUs, newFMUs) ==
(sameSetOfFMUs(oldFMUs, newFMUs) and pre_sameSetOfFMUs(oldFMUs, newFMUs))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 720:41\<close>
definition
	pre_fmusNotAffected :: "FMU VDMSet \<Rightarrow> FMU VDMSet \<Rightarrow> bool"
where
	"pre_fmusNotAffected oldFMUs   newFMUs \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `pre_fmusNotAffected` specification.\<close>
		((inv_VDMSet' inv_FMU  oldFMUs)  \<and>  (inv_VDMSet' inv_FMU  newFMUs))  \<and> 
		\<comment>\<open>User defined body of pre_fmusNotAffected.\<close>
		((sameSetOfFMUs oldFMUs   newFMUs) \<and> (pre_sameSetOfFMUs oldFMUs   newFMUs))"


\<comment>\<open>VDM source: post_fmusNotAffected: (set of (FMU) * set of (FMU) * bool +> bool)
	post_fmusNotAffected(oldFMUs, newFMUs, RESULT) ==
null\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 718:5\<close>
definition
	post_fmusNotAffected :: "FMU VDMSet \<Rightarrow> FMU VDMSet \<Rightarrow> bool \<Rightarrow> bool"
where
	"post_fmusNotAffected oldFMUs   newFMUs   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_fmusNotAffected` specification.\<close>
		((inv_VDMSet' inv_FMU  oldFMUs)  \<and>  (inv_VDMSet' inv_FMU  newFMUs)  \<and>  (inv_bool RESULT))"

definition
	fmusNotAffected :: "FMU VDMSet \<Rightarrow> FMU VDMSet \<Rightarrow> bool"
where
	"fmusNotAffected oldFMUs   newFMUs \<equiv> 
	\<comment>\<open>User defined body of fmusNotAffected.\<close>
	(oldFMUs = newFMUs)"

	
	
\<comment>\<open>VDM source: updateEnvironmentEquation: (Importer * FMU * FMURef -> Importer)
	updateEnvironmentEquation(I, fmu, equation) ==
let triggeredClocks:set of (Clock) = {clock | clock in set (fmu.clocks) & ((equation.ref) in set (clock.dependsOn))} in let triggeredInputs:set of (FMURef) = {mk_FMURef((equation.name), (inputClock.ref)) | inputClock in set triggeredClocks & ((inputClock.type) <> <input>)}, triggeredOutputs:set of (FMURef) = {mk_FMURef((equation.name), (outputClock.ref)) | outputClock in set triggeredClocks & ((outputClock.type) <> <output>)} in mu(I, scenario |-> mu((I.scenario), fmus |-> (((I.scenario).fmus) ++ {(fmu.name) |-> fmu})), calculatedEquations |-> ((I.calculatedEquations) union {equation}), relevantInputClocks |-> ((I.relevantInputClocks) union triggeredInputs), relevantOutputClocks |-> ((I.relevantOutputClocks) union triggeredOutputs))
	pre ((equation in set ((I.activeEquations) \ (I.calculatedEquations))) and ((fmu.mode) = <EVENT>))
	post ((equation in set (RESULT.calculatedEquations)) and (((I.relevantInputClocks) subset (RESULT.relevantInputClocks)) and (((I.relevantOutputClocks) subset (RESULT.relevantOutputClocks)) and let resultFMUs:set of (FMU) = (rng ({(fmu.name)} <-: ((RESULT.scenario).fmus))), oldFMUs:set of (FMU) = (rng ({(fmu.name)} <-: ((I.scenario).fmus))) in (pre_fmusNotAffected(oldFMUs, resultFMUs) and fmusNotAffected(oldFMUs, resultFMUs)))))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 722:5\<close>

\<comment>\<open>VDM source: pre_updateEnvironmentEquation: (Importer * FMU * FMURef +> bool)
	pre_updateEnvironmentEquation(I, fmu, equation) ==
((equation in set ((I.activeEquations) \ (I.calculatedEquations))) and ((fmu.mode) = <EVENT>))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 735:9\<close>
definition
	pre_updateEnvironmentEquation :: "Importer \<Rightarrow> FMU \<Rightarrow> FMURef \<Rightarrow> bool"
where
	"pre_updateEnvironmentEquation I   fmu   equation \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `pre_updateEnvironmentEquation` specification.\<close>
		(inv_Importer I  \<and>  inv_FMU fmu  \<and>  inv_FMURef equation)  \<and> 
		\<comment>\<open>User defined body of pre_updateEnvironmentEquation.\<close>
		((equation \<in> ((activeEquations\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I) - (calculatedEquations\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I))) \<and> ((mode\<^sub>F\<^sub>M\<^sub>U fmu) = FMUMode.U_EVENT ))"


\<comment>\<open>VDM source: post_updateEnvironmentEquation: (Importer * FMU * FMURef * Importer +> bool)
	post_updateEnvironmentEquation(I, fmu, equation, RESULT) ==
((equation in set (RESULT.calculatedEquations)) and (((I.relevantInputClocks) subset (RESULT.relevantInputClocks)) and (((I.relevantOutputClocks) subset (RESULT.relevantOutputClocks)) and let resultFMUs:set of (FMU) = (rng ({(fmu.name)} <-: ((RESULT.scenario).fmus))), oldFMUs:set of (FMU) = (rng ({(fmu.name)} <-: ((I.scenario).fmus))) in (pre_fmusNotAffected(oldFMUs, resultFMUs) and fmusNotAffected(oldFMUs, resultFMUs)))))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 737:9\<close>
definition
	post_updateEnvironmentEquation :: "Importer \<Rightarrow> FMU \<Rightarrow> FMURef \<Rightarrow> Importer \<Rightarrow> bool"
where
	"post_updateEnvironmentEquation I   fmu   equation   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `post_updateEnvironmentEquation` specification.\<close>
		(inv_Importer I  \<and>  inv_FMU fmu  \<and>  inv_FMURef equation  \<and>  inv_Importer RESULT)  \<and> 
		\<comment>\<open>User defined body of post_updateEnvironmentEquation.\<close>
		((equation \<in> (calculatedEquations\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r RESULT)) \<and> (((relevantInputClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I) \<subseteq> (relevantInputClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r RESULT)) \<and> (((relevantOutputClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I) \<subseteq> (relevantOutputClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r RESULT)) \<and> (
		let 
(resultFMUs::FMU VDMSet) = (rng ({(name\<^sub>F\<^sub>M\<^sub>U fmu)} -\<triangleleft> (fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r RESULT))))
		;
		
(oldFMUs::FMU VDMSet) = (rng ({(name\<^sub>F\<^sub>M\<^sub>U fmu)} -\<triangleleft> (fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I))))
		in
			(if ((inv_VDMSet' inv_FMU  resultFMUs))
	 \<and> 
	((inv_VDMSet' inv_FMU  oldFMUs)) then
			((pre_fmusNotAffected oldFMUs   resultFMUs) \<and> (fmusNotAffected oldFMUs   resultFMUs))
		 else
			undefined
		)
		))))"

definition
	updateEnvironmentEquation :: "Importer \<Rightarrow> FMU \<Rightarrow> FMURef \<Rightarrow> Importer"
where
	"updateEnvironmentEquation I   fmu   equation \<equiv> 
	\<comment>\<open>User defined body of updateEnvironmentEquation.\<close>
	(
		let 
(triggeredClocks::Clock VDMSet) = { clock .   ((clock \<in>(clocks\<^sub>F\<^sub>M\<^sub>U fmu)))  \<and> ((ref\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f equation) \<in> (dependsOn\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k clock)) }
		in
			(if ((inv_VDMSet' inv_Clock  triggeredClocks)) then
			(
		let 
(triggeredInputs::FMURef VDMSet) = { \<lparr>name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f = (name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f equation), ref\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f = (ref\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k inputClock)\<rparr> | inputClock .  ((inputClock \<in>triggeredClocks))  \<and> ((type\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k inputClock) \<noteq> Causality.U_input ) }
		;
		
(triggeredOutputs::FMURef VDMSet) = { \<lparr>name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f = (name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f equation), ref\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f = (ref\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k outputClock)\<rparr> | outputClock .  ((outputClock \<in>triggeredClocks))  \<and> ((type\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k outputClock) \<noteq> Causality.U_output ) }
		in
			(if ((inv_VDMSet' inv_FMURef  triggeredInputs))
	 \<and> 
	((inv_VDMSet' inv_FMURef  triggeredOutputs)) then
			(I)\<lparr>scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r := ((scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I))\<lparr>fmus\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r := ((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) \<dagger> [(name\<^sub>F\<^sub>M\<^sub>U fmu)\<mapsto>fmu])\<rparr>, calculatedEquations\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r := ((calculatedEquations\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I) \<union> {equation}), relevantInputClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r := ((relevantInputClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I) \<union> triggeredInputs), relevantOutputClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r := ((relevantOutputClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I) \<union> triggeredOutputs)\<rparr>
		 else
			undefined
		)
		)
		 else
			undefined
		)
		)"

	
	
\<comment>\<open>VDM source: preSetI: (Importer * FMU * Ref -> bool)
	preSetI(I, fmu, port) ==
let inputVar:Variable = derefInput(fmu, port), fmuRef:FMURef = mk_FMURef((fmu.name), port) in ((((fmu.mode) = <EVENT>) <=> ((fmuRef in set ((I.activeEquations) \ (I.calculatedEquations))) and ((inputVar.type) = <discrete>))) and ((fmuRef in set (dom (I.valueMap))) and let val:FMIValue = (I.valueMap)(fmuRef) in ((((fmu.mode) = <STEP>) => (((inputVar.type) = <continous>) and ((((inputVar.contract) = <reactive>) => ((val.time) > (fmu.time))) and (((inputVar.contract) = <delayed>) => ((val.time) = (fmu.time)))))) and preSet(fmu, port))))
	pre (pre_derefInput(fmu, port) and pre_preSet(fmu, port))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 752:5\<close>

\<comment>\<open>VDM source: pre_preSetI: (Importer * FMU * Ref +> bool)
	pre_preSetI(I, fmu, port) ==
(pre_derefInput(fmu, port) and pre_preSet(fmu, port))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 763:35\<close>
definition
	pre_preSetI :: "Importer \<Rightarrow> FMU \<Rightarrow> Ref \<Rightarrow> bool"
where
	"pre_preSetI I   fmu   port \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `pre_preSetI` specification.\<close>
		(inv_Importer I  \<and>  inv_FMU fmu  \<and>  (inv_Ref port))  \<and> 
		\<comment>\<open>User defined body of pre_preSetI.\<close>
		((pre_derefInput fmu   port) \<and> (pre_preSet fmu   port))"


\<comment>\<open>VDM source: post_preSetI: (Importer * FMU * Ref * bool +> bool)
	post_preSetI(I, fmu, port, RESULT) ==
null\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 752:5\<close>
definition
	post_preSetI :: "Importer \<Rightarrow> FMU \<Rightarrow> Ref \<Rightarrow> bool \<Rightarrow> bool"
where
	"post_preSetI I   fmu   port   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_preSetI` specification.\<close>
		(inv_Importer I  \<and>  inv_FMU fmu  \<and>  (inv_Ref port)  \<and>  (inv_bool RESULT))"

definition
	preSetI :: "Importer \<Rightarrow> FMU \<Rightarrow> Ref \<Rightarrow> bool"
where
	"preSetI I   fmu   port \<equiv> 
	\<comment>\<open>User defined body of preSetI.\<close>
	(
		let 
(inputVar::Variable) = (derefInput fmu   port)
		;
		
(fmuRef::FMURef) = \<lparr>name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f = (name\<^sub>F\<^sub>M\<^sub>U fmu), ref\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f = port\<rparr>
		in
			(if (inv_Variable inputVar)
	 \<and> 
	(inv_FMURef fmuRef) then
			((((mode\<^sub>F\<^sub>M\<^sub>U fmu) = FMUMode.U_EVENT ) \<longleftrightarrow> ((fmuRef \<in> ((activeEquations\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I) - (calculatedEquations\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I))) \<and> ((type\<^sub>V\<^sub>a\<^sub>r\<^sub>i\<^sub>a\<^sub>b\<^sub>l\<^sub>e inputVar) = PortType.U_discrete ))) \<and> ((fmuRef \<in> (dom (valueMap\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I))) \<and> (
		let 
(val::FMIValue) = (the(((valueMap\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I) fmuRef)))
		in
			(if (inv_FMIValue val) then
			((((mode\<^sub>F\<^sub>M\<^sub>U fmu) = FMUMode.U_STEP ) \<longrightarrow> (((type\<^sub>V\<^sub>a\<^sub>r\<^sub>i\<^sub>a\<^sub>b\<^sub>l\<^sub>e inputVar) = PortType.U_continous ) \<and> ((((contract\<^sub>V\<^sub>a\<^sub>r\<^sub>i\<^sub>a\<^sub>b\<^sub>l\<^sub>e inputVar) = Contract.U_reactive ) \<longrightarrow> \<comment>\<open>Transform a VDM `>` expression into a reversed `ord_Time` call\<close>
	(ord_Time (time\<^sub>F\<^sub>M\<^sub>U fmu)   (time\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e val))) \<and> (((contract\<^sub>V\<^sub>a\<^sub>r\<^sub>i\<^sub>a\<^sub>b\<^sub>l\<^sub>e inputVar) = Contract.U_delayed ) \<longrightarrow> \<comment>\<open>Transform a VDM `=` expression into an `eq_Time` call\<close>
	(eq_Time (time\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e val)   (time\<^sub>F\<^sub>M\<^sub>U fmu)))))) \<and> (preSet fmu   port))
		 else
			undefined
		)
		)))
		 else
			undefined
		)
		)"

	
	
\<comment>\<open>VDM source: setPort: (Importer * FMURef -> Importer)
	setPort(I, port) ==
let fmi_value:FMIValue = (I.valueMap)(port) in let fmu:FMU = set_m(((I.scenario).fmus)((port.name)), (port.ref), fmi_value) in mu(I, scenario |-> mu((I.scenario), fmus |-> (((I.scenario).fmus) ++ {(fmu.name) |-> fmu})), valueMap |-> ({port} <-: (I.valueMap)))
	pre (pre_preSetI(I, ((I.scenario).fmus)((port.name)), (port.ref)) and (preSetI(I, ((I.scenario).fmus)((port.name)), (port.ref)) and ((port in set (dom (I.valueMap))) and pre_set_m(((I.scenario).fmus)((port.name)), (port.ref), (I.valueMap)(port)))))
	post let oldFMUs:set of (FMU) = (rng ({(port.name)} <-: ((I.scenario).fmus))), resultFMUs:set of (FMU) = (rng ({(port.name)} <-: ((RESULT.scenario).fmus))) in (pre_fmusNotAffected(oldFMUs, resultFMUs) and (fmusNotAffected(oldFMUs, resultFMUs) and (((card (dom (RESULT.valueMap))) + 1) = (card (dom (I.valueMap))))))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 767:5\<close>

\<comment>\<open>VDM source: pre_setPort: (Importer * FMURef +> bool)
	pre_setPort(I, port) ==
(pre_preSetI(I, ((I.scenario).fmus)((port.name)), (port.ref)) and (preSetI(I, ((I.scenario).fmus)((port.name)), (port.ref)) and ((port in set (dom (I.valueMap))) and pre_set_m(((I.scenario).fmus)((port.name)), (port.ref), (I.valueMap)(port)))))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 776:9\<close>
definition
	pre_setPort :: "Importer \<Rightarrow> FMURef \<Rightarrow> bool"
where
	"pre_setPort I   port \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `pre_setPort` specification.\<close>
		(inv_Importer I  \<and>  inv_FMURef port)  \<and> 
		\<comment>\<open>User defined body of pre_setPort.\<close>
		((pre_preSetI I   ((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) (name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f port))   (ref\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f port)) \<and> ((preSetI I   ((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) (name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f port))   (ref\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f port)) \<and> ((port \<in> (dom (valueMap\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I))) \<and> (pre_set_m ((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) (name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f port))   (ref\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f port)   ((valueMap\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I) port)))))"


\<comment>\<open>VDM source: post_setPort: (Importer * FMURef * Importer +> bool)
	post_setPort(I, port, RESULT) ==
let oldFMUs:set of (FMU) = (rng ({(port.name)} <-: ((I.scenario).fmus))), resultFMUs:set of (FMU) = (rng ({(port.name)} <-: ((RESULT.scenario).fmus))) in (pre_fmusNotAffected(oldFMUs, resultFMUs) and (fmusNotAffected(oldFMUs, resultFMUs) and (((card (dom (RESULT.valueMap))) + 1) = (card (dom (I.valueMap))))))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 780:9\<close>
definition
	post_setPort :: "Importer \<Rightarrow> FMURef \<Rightarrow> Importer \<Rightarrow> bool"
where
	"post_setPort I   port   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `post_setPort` specification.\<close>
		(inv_Importer I  \<and>  inv_FMURef port  \<and>  inv_Importer RESULT)  \<and> 
		\<comment>\<open>User defined body of post_setPort.\<close>
		(
		let 
(oldFMUs::FMU VDMSet) = (rng ({(name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f port)} -\<triangleleft> (fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I))))
		;
		
(resultFMUs::FMU VDMSet) = (rng ({(name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f port)} -\<triangleleft> (fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r RESULT))))
		in
			(if ((inv_VDMSet' inv_FMU  oldFMUs))
	 \<and> 
	((inv_VDMSet' inv_FMU  resultFMUs)) then
			((pre_fmusNotAffected oldFMUs   resultFMUs) \<and> ((fmusNotAffected oldFMUs   resultFMUs) \<and> (((vdm_card (dom (valueMap\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r RESULT))) + (1::VDMNat1)) = (vdm_card (dom (valueMap\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I))))))
		 else
			undefined
		)
		)"

definition
	setPort :: "Importer \<Rightarrow> FMURef \<Rightarrow> Importer"
where
	"setPort I   port \<equiv> 
	\<comment>\<open>User defined body of setPort.\<close>
	(
		let 
(fmi_value::FMIValue) = (the(((valueMap\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I) port)))
		in
			(if (inv_FMIValue fmi_value) then
			(
		let 
(fmu::FMU) = (set_m ((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) (name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f port))   (ref\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f port)   fmi_value)
		in
			(if (inv_FMU fmu) then
			(I)\<lparr>scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r := ((scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I))\<lparr>fmus\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r := ((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) \<dagger> [(name\<^sub>F\<^sub>M\<^sub>U fmu)\<mapsto>fmu])\<rparr>, valueMap\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r := ({port} -\<triangleleft> (valueMap\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I))\<rparr>
		 else
			undefined
		)
		)
		 else
			undefined
		)
		)"

	
	
\<comment>\<open>VDM source: calculateInput: (Importer * FMURef -> Importer)
	calculateInput(I, equation) ==
let I1:Importer = setPort(I, equation) in updateEnvironmentEquation(I1, ((I.scenario).fmus)((equation.name)), equation)
	pre (((equation.name) in set (dom ((I.scenario).fmus))) and (pre_setPort(I, equation) and (pre_updateEnvironmentEquation(setPort(I, equation), ((I.scenario).fmus)((equation.name)), equation) and let fmu:FMU = ((I.scenario).fmus)((equation.name)) in ((equation in set ((I.activeEquations) \ (I.calculatedEquations))) and (((fmu.mode) = <EVENT>) and (pre_preSetI(I, fmu, (equation.ref)) and preSetI(I, fmu, (equation.ref))))))))
	post let newFMU:FMU = ((RESULT.scenario).fmus)((equation.name)), oldFMU:FMU = ((I.scenario).fmus)((equation.name)) in (((newFMU.mode) = (oldFMU.mode)) and (((newFMU.time) = (oldFMU.time)) and ((((newFMU.io).LFoutput) = ((oldFMU.io).LFoutput)) and (pre_fmusNotAffected((rng ({(equation.name)} <-: ((I.scenario).fmus))), (rng ({(equation.name)} <-: ((RESULT.scenario).fmus)))) and (fmusNotAffected((rng ({(equation.name)} <-: ((I.scenario).fmus))), (rng ({(equation.name)} <-: ((RESULT.scenario).fmus)))) and (equation in set (RESULT.calculatedEquations)))))))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 790:5\<close>

\<comment>\<open>VDM source: pre_calculateInput: (Importer * FMURef +> bool)
	pre_calculateInput(I, equation) ==
(((equation.name) in set (dom ((I.scenario).fmus))) and (pre_setPort(I, equation) and (pre_updateEnvironmentEquation(setPort(I, equation), ((I.scenario).fmus)((equation.name)), equation) and let fmu:FMU = ((I.scenario).fmus)((equation.name)) in ((equation in set ((I.activeEquations) \ (I.calculatedEquations))) and (((fmu.mode) = <EVENT>) and (pre_preSetI(I, fmu, (equation.ref)) and preSetI(I, fmu, (equation.ref))))))))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 797:9\<close>
definition
	pre_calculateInput :: "Importer \<Rightarrow> FMURef \<Rightarrow> bool"
where
	"pre_calculateInput I   equation \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `pre_calculateInput` specification.\<close>
		(inv_Importer I  \<and>  inv_FMURef equation)  \<and> 
		\<comment>\<open>User defined body of pre_calculateInput.\<close>
		(((name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f equation) \<in> (dom (fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)))) \<and> ((pre_setPort I   equation) \<and> ((pre_updateEnvironmentEquation (setPort I   equation)   ((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) (name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f equation))   equation) \<and> (
		let 
(fmu::FMU) = (the(((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) (name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f equation))))
		in
			(if (inv_FMU fmu) then
			((equation \<in> ((activeEquations\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I) - (calculatedEquations\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I))) \<and> (((mode\<^sub>F\<^sub>M\<^sub>U fmu) = FMUMode.U_EVENT ) \<and> ((pre_preSetI I   fmu   (ref\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f equation)) \<and> (preSetI I   fmu   (ref\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f equation)))))
		 else
			undefined
		)
		))))"


\<comment>\<open>VDM source: post_calculateInput: (Importer * FMURef * Importer +> bool)
	post_calculateInput(I, equation, RESULT) ==
let newFMU:FMU = ((RESULT.scenario).fmus)((equation.name)), oldFMU:FMU = ((I.scenario).fmus)((equation.name)) in (((newFMU.mode) = (oldFMU.mode)) and (((newFMU.time) = (oldFMU.time)) and ((((newFMU.io).LFoutput) = ((oldFMU.io).LFoutput)) and (pre_fmusNotAffected((rng ({(equation.name)} <-: ((I.scenario).fmus))), (rng ({(equation.name)} <-: ((RESULT.scenario).fmus)))) and (fmusNotAffected((rng ({(equation.name)} <-: ((I.scenario).fmus))), (rng ({(equation.name)} <-: ((RESULT.scenario).fmus)))) and (equation in set (RESULT.calculatedEquations)))))))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 806:5\<close>
definition
	post_calculateInput :: "Importer \<Rightarrow> FMURef \<Rightarrow> Importer \<Rightarrow> bool"
where
	"post_calculateInput I   equation   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `post_calculateInput` specification.\<close>
		(inv_Importer I  \<and>  inv_FMURef equation  \<and>  inv_Importer RESULT)  \<and> 
		\<comment>\<open>User defined body of post_calculateInput.\<close>
		(
		let 
(newFMU::FMU) = (the(((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r RESULT)) (name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f equation))))
		;
		
(oldFMU::FMU) = (the(((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) (name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f equation))))
		in
			(if (inv_FMU newFMU)
	 \<and> 
	(inv_FMU oldFMU) then
			(((mode\<^sub>F\<^sub>M\<^sub>U newFMU) = (mode\<^sub>F\<^sub>M\<^sub>U oldFMU)) \<and> (\<comment>\<open>Transform a VDM `=` expression into an `eq_Time` call\<close>
	(eq_Time (time\<^sub>F\<^sub>M\<^sub>U newFMU)   (time\<^sub>F\<^sub>M\<^sub>U oldFMU)) \<and> (((LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U newFMU)) = (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U oldFMU))) \<and> ((pre_fmusNotAffected (rng ({(name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f equation)} -\<triangleleft> (fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I))))   (rng ({(name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f equation)} -\<triangleleft> (fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r RESULT))))) \<and> ((fmusNotAffected (rng ({(name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f equation)} -\<triangleleft> (fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I))))   (rng ({(name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f equation)} -\<triangleleft> (fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r RESULT))))) \<and> (equation \<in> (calculatedEquations\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r RESULT)))))))
		 else
			undefined
		)
		)"

definition
	calculateInput :: "Importer \<Rightarrow> FMURef \<Rightarrow> Importer"
where
	"calculateInput I   equation \<equiv> 
	\<comment>\<open>User defined body of calculateInput.\<close>
	(
		let 
(I1::Importer) = (setPort I   equation)
		in
			(if (inv_Importer I1) then
			(updateEnvironmentEquation I1   ((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) (name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f equation))   equation)
		 else
			undefined
		)
		)"

	
	
\<comment>\<open>VDM source: preGetI: (Importer * FMU * Ref -> bool)
	preGetI(I, fmu, port) ==
let outputVar:Variable = derefOutput(fmu, port), fmuRef:FMURef = mk_FMURef((fmu.name), port), connectedInput:FMURef = (((I.scenario).connections).dataConnections)(fmuRef) in let input:Variable = derefInput(((I.scenario).fmus)((connectedInput.name)), (connectedInput.ref)) in ((((fmu.mode) = <EVENT>) <=> ((fmuRef in set ((I.activeEquations) \ (I.calculatedEquations))) and ((outputVar.type) = <discrete>))) and ((((fmu.mode) = <STEP>) => (((outputVar.type) = <continous>) and (((input.contract) = <delayed>) => (fmu.stepped)))) and (preGet(fmu, port) and (connectedInput not in set (dom (I.valueMap))))))
	pre (pre_preGet(fmu, port) and (pre_derefOutput(fmu, port) and let fmuRef:FMURef = mk_FMURef((fmu.name), port), connectedInput:FMURef = (((I.scenario).connections).dataConnections)(fmuRef) in ((fmuRef in set (dom (((I.scenario).connections).dataConnections))) and pre_derefInput(((I.scenario).fmus)((connectedInput.name)), (connectedInput.ref)))))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 817:5\<close>

\<comment>\<open>VDM source: pre_preGetI: (Importer * FMU * Ref +> bool)
	pre_preGetI(I, fmu, port) ==
(pre_preGet(fmu, port) and (pre_derefOutput(fmu, port) and let fmuRef:FMURef = mk_FMURef((fmu.name), port), connectedInput:FMURef = (((I.scenario).connections).dataConnections)(fmuRef) in ((fmuRef in set (dom (((I.scenario).connections).dataConnections))) and pre_derefInput(((I.scenario).fmus)((connectedInput.name)), (connectedInput.ref)))))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 828:9\<close>
definition
	pre_preGetI :: "Importer \<Rightarrow> FMU \<Rightarrow> Ref \<Rightarrow> bool"
where
	"pre_preGetI I   fmu   port \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `pre_preGetI` specification.\<close>
		(inv_Importer I  \<and>  inv_FMU fmu  \<and>  (inv_Ref port))  \<and> 
		\<comment>\<open>User defined body of pre_preGetI.\<close>
		((pre_preGet fmu   port) \<and> ((pre_derefOutput fmu   port) \<and> (
		let 
(fmuRef::FMURef) = \<lparr>name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f = (name\<^sub>F\<^sub>M\<^sub>U fmu), ref\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f = port\<rparr>
		;
		
(connectedInput::FMURef) = (the(((dataConnections\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o\<^sub>C\<^sub>o\<^sub>n\<^sub>n\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n\<^sub>s (connections\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I))) fmuRef)))
		in
			(if (inv_FMURef fmuRef)
	 \<and> 
	(inv_FMURef connectedInput) then
			((fmuRef \<in> (dom (dataConnections\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o\<^sub>C\<^sub>o\<^sub>n\<^sub>n\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n\<^sub>s (connections\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I))))) \<and> (pre_derefInput ((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) (name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f connectedInput))   (ref\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f connectedInput)))
		 else
			undefined
		)
		)))"


\<comment>\<open>VDM source: post_preGetI: (Importer * FMU * Ref * bool +> bool)
	post_preGetI(I, fmu, port, RESULT) ==
null\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 817:5\<close>
definition
	post_preGetI :: "Importer \<Rightarrow> FMU \<Rightarrow> Ref \<Rightarrow> bool \<Rightarrow> bool"
where
	"post_preGetI I   fmu   port   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_preGetI` specification.\<close>
		(inv_Importer I  \<and>  inv_FMU fmu  \<and>  (inv_Ref port)  \<and>  (inv_bool RESULT))"

definition
	preGetI :: "Importer \<Rightarrow> FMU \<Rightarrow> Ref \<Rightarrow> bool"
where
	"preGetI I   fmu   port \<equiv> 
	\<comment>\<open>User defined body of preGetI.\<close>
	(
		let 
(outputVar::Variable) = (derefOutput fmu   port)
		;
		
(fmuRef::FMURef) = \<lparr>name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f = (name\<^sub>F\<^sub>M\<^sub>U fmu), ref\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f = port\<rparr>
		;
		
(connectedInput::FMURef) = (the(((dataConnections\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o\<^sub>C\<^sub>o\<^sub>n\<^sub>n\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n\<^sub>s (connections\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I))) fmuRef)))
		in
			(if (inv_Variable outputVar)
	 \<and> 
	(inv_FMURef fmuRef)
	 \<and> 
	(inv_FMURef connectedInput) then
			(
		let 
(input::Variable) = (derefInput ((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) (name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f connectedInput))   (ref\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f connectedInput))
		in
			(if (inv_Variable input) then
			((((mode\<^sub>F\<^sub>M\<^sub>U fmu) = FMUMode.U_EVENT ) \<longleftrightarrow> ((fmuRef \<in> ((activeEquations\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I) - (calculatedEquations\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I))) \<and> ((type\<^sub>V\<^sub>a\<^sub>r\<^sub>i\<^sub>a\<^sub>b\<^sub>l\<^sub>e outputVar) = PortType.U_discrete ))) \<and> ((((mode\<^sub>F\<^sub>M\<^sub>U fmu) = FMUMode.U_STEP ) \<longrightarrow> (((type\<^sub>V\<^sub>a\<^sub>r\<^sub>i\<^sub>a\<^sub>b\<^sub>l\<^sub>e outputVar) = PortType.U_continous ) \<and> (((contract\<^sub>V\<^sub>a\<^sub>r\<^sub>i\<^sub>a\<^sub>b\<^sub>l\<^sub>e input) = Contract.U_delayed ) \<longrightarrow> (stepped\<^sub>F\<^sub>M\<^sub>U fmu)))) \<and> ((preGet fmu   port) \<and> (connectedInput \<notin> (dom (valueMap\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I))))))
		 else
			undefined
		)
		)
		 else
			undefined
		)
		)"

	
	
\<comment>\<open>VDM source: getPort: (Importer * FMURef -> Importer)
	getPort(I, port) ==
let mk_(fmu, val):(FMU * FMIValue) = get_m(((I.scenario).fmus)((port.name)), (port.ref)), connectedInput:FMURef = (((I.scenario).connections).dataConnections)(port) in mu(I, scenario |-> mu((I.scenario), fmus |-> (((I.scenario).fmus) ++ {(fmu.name) |-> fmu})), valueMap |-> ((I.valueMap) ++ {connectedInput |-> val}))
	pre (pre_preGetI(I, ((I.scenario).fmus)((port.name)), (port.ref)) and (preGetI(I, ((I.scenario).fmus)((port.name)), (port.ref)) and pre_get_m(((I.scenario).fmus)((port.name)), (port.ref))))
	post (((card (dom (RESULT.valueMap))) = ((card (dom (I.valueMap))) + 1)) and let oldFMUs:set of (FMU) = (rng ({(port.name)} <-: ((I.scenario).fmus))), resultFMUs:set of (FMU) = (rng ({(port.name)} <-: ((RESULT.scenario).fmus))) in (pre_fmusNotAffected(oldFMUs, resultFMUs) and fmusNotAffected(oldFMUs, resultFMUs)))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 836:5\<close>

\<comment>\<open>VDM source: pre_getPort: (Importer * FMURef +> bool)
	pre_getPort(I, port) ==
(pre_preGetI(I, ((I.scenario).fmus)((port.name)), (port.ref)) and (preGetI(I, ((I.scenario).fmus)((port.name)), (port.ref)) and pre_get_m(((I.scenario).fmus)((port.name)), (port.ref))))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 845:9\<close>
definition
	pre_getPort :: "Importer \<Rightarrow> FMURef \<Rightarrow> bool"
where
	"pre_getPort I   port \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `pre_getPort` specification.\<close>
		(inv_Importer I  \<and>  inv_FMURef port)  \<and> 
		\<comment>\<open>User defined body of pre_getPort.\<close>
		((pre_preGetI I   ((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) (name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f port))   (ref\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f port)) \<and> ((preGetI I   ((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) (name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f port))   (ref\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f port)) \<and> (pre_get_m ((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) (name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f port))   (ref\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f port))))"


\<comment>\<open>VDM source: post_getPort: (Importer * FMURef * Importer +> bool)
	post_getPort(I, port, RESULT) ==
(((card (dom (RESULT.valueMap))) = ((card (dom (I.valueMap))) + 1)) and let oldFMUs:set of (FMU) = (rng ({(port.name)} <-: ((I.scenario).fmus))), resultFMUs:set of (FMU) = (rng ({(port.name)} <-: ((RESULT.scenario).fmus))) in (pre_fmusNotAffected(oldFMUs, resultFMUs) and fmusNotAffected(oldFMUs, resultFMUs)))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 849:9\<close>
definition
	post_getPort :: "Importer \<Rightarrow> FMURef \<Rightarrow> Importer \<Rightarrow> bool"
where
	"post_getPort I   port   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `post_getPort` specification.\<close>
		(inv_Importer I  \<and>  inv_FMURef port  \<and>  inv_Importer RESULT)  \<and> 
		\<comment>\<open>User defined body of post_getPort.\<close>
		(((vdm_card (dom (valueMap\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r RESULT))) = ((vdm_card (dom (valueMap\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I))) + (1::VDMNat1))) \<and> (
		let 
(oldFMUs::FMU VDMSet) = (rng ({(name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f port)} -\<triangleleft> (fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I))))
		;
		
(resultFMUs::FMU VDMSet) = (rng ({(name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f port)} -\<triangleleft> (fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r RESULT))))
		in
			(if ((inv_VDMSet' inv_FMU  oldFMUs))
	 \<and> 
	((inv_VDMSet' inv_FMU  resultFMUs)) then
			((pre_fmusNotAffected oldFMUs   resultFMUs) \<and> (fmusNotAffected oldFMUs   resultFMUs))
		 else
			undefined
		)
		))"

definition
	getPort :: "Importer \<Rightarrow> FMURef \<Rightarrow> Importer"
where
	"getPort I   port \<equiv> 
	\<comment>\<open>User defined body of getPort.\<close>
	(
		let 
(fmu::FMU) = (get_m ((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) (name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f port))   (ref\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f port));
(val::FMIValue) = (get_m ((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) (name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f port))   (ref\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f port))
		;
		
(connectedInput::FMURef) = (the(((dataConnections\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o\<^sub>C\<^sub>o\<^sub>n\<^sub>n\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n\<^sub>s (connections\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I))) port)))
		in
			(if (
		( (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U (fst dummy0)))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U (fst dummy0))))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U (fst dummy0)))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U (fst dummy0))))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U (fst dummy0)))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U (fst dummy0)))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U (fst dummy0)))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U (fst dummy0))))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U (fst dummy0)))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U (fst dummy0))))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U (fst dummy0))))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U (fst dummy0)))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U (fst dummy0)))) )\<and>
		  ((((case (fmiValue\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e (snd dummy0)) of
		 ValueType.U_bool (fmiValue\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e (snd dummy0)) \<Rightarrow> (inv_bool (fmiValue\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e (snd dummy0)))
		  | ValueType.U_VDMReal (fmiValue\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e (snd dummy0)) \<Rightarrow> (inv_VDMReal (fmiValue\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e (snd dummy0)))
		 ))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e (snd dummy0)))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e (snd dummy0))))) )) )
		))
	 \<and> 
	(inv_FMURef connectedInput) then
			(I)\<lparr>scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r := ((scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I))\<lparr>fmus\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r := ((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) \<dagger> [(name\<^sub>F\<^sub>M\<^sub>U fmu)\<mapsto>fmu])\<rparr>, valueMap\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r := ((valueMap\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I) \<dagger> [connectedInput\<mapsto>val])\<rparr>
		 else
			undefined
		)
		)"

	
	
\<comment>\<open>VDM source: postVariableCalculation: (FMURef * Importer * Importer -> bool)
	postVariableCalculation(equation, I, NewI) ==
((equation in set (NewI.calculatedEquations)) and (((I.relevantInputClocks) = (NewI.relevantInputClocks)) and (((I.relevantOutputClocks) subset (NewI.relevantOutputClocks)) and (((I.calculatedEquations) subset (NewI.calculatedEquations)) and let fmu:FMU = ((NewI.scenario).fmus)((equation.name)) in (pre_fmusNotAffected((rng ({(fmu.name)} <-: ((I.scenario).fmus))), (rng ({(fmu.name)} <-: ((NewI.scenario).fmus)))) and (fmusNotAffected((rng ({(fmu.name)} <-: ((I.scenario).fmus))), (rng ({(fmu.name)} <-: ((NewI.scenario).fmus)))) and ((fmu.mode) = <EVENT>)))))))
	pre ((equation.name) in set (dom ((NewI.scenario).fmus)))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 856:5\<close>

\<comment>\<open>VDM source: pre_postVariableCalculation: (FMURef * Importer * Importer +> bool)
	pre_postVariableCalculation(equation, I, NewI) ==
((equation.name) in set (dom ((NewI.scenario).fmus)))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 866:23\<close>
definition
	pre_postVariableCalculation :: "FMURef \<Rightarrow> Importer \<Rightarrow> Importer \<Rightarrow> bool"
where
	"pre_postVariableCalculation equation   I   NewI \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `pre_postVariableCalculation` specification.\<close>
		(inv_FMURef equation  \<and>  inv_Importer I  \<and>  inv_Importer NewI)  \<and> 
		\<comment>\<open>User defined body of pre_postVariableCalculation.\<close>
		((name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f equation) \<in> (dom (fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r NewI))))"


\<comment>\<open>VDM source: post_postVariableCalculation: (FMURef * Importer * Importer * bool +> bool)
	post_postVariableCalculation(equation, I, NewI, RESULT) ==
null\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 856:5\<close>
definition
	post_postVariableCalculation :: "FMURef \<Rightarrow> Importer \<Rightarrow> Importer \<Rightarrow> bool \<Rightarrow> bool"
where
	"post_postVariableCalculation equation   I   NewI   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_postVariableCalculation` specification.\<close>
		(inv_FMURef equation  \<and>  inv_Importer I  \<and>  inv_Importer NewI  \<and>  (inv_bool RESULT))"

definition
	postVariableCalculation :: "FMURef \<Rightarrow> Importer \<Rightarrow> Importer \<Rightarrow> bool"
where
	"postVariableCalculation equation   I   NewI \<equiv> 
	\<comment>\<open>User defined body of postVariableCalculation.\<close>
	((equation \<in> (calculatedEquations\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r NewI)) \<and> (((relevantInputClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I) = (relevantInputClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r NewI)) \<and> (((relevantOutputClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I) \<subseteq> (relevantOutputClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r NewI)) \<and> (((calculatedEquations\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I) \<subseteq> (calculatedEquations\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r NewI)) \<and> (
		let 
(fmu::FMU) = (the(((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r NewI)) (name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f equation))))
		in
			(if (inv_FMU fmu) then
			((pre_fmusNotAffected (rng ({(name\<^sub>F\<^sub>M\<^sub>U fmu)} -\<triangleleft> (fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I))))   (rng ({(name\<^sub>F\<^sub>M\<^sub>U fmu)} -\<triangleleft> (fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r NewI))))) \<and> ((fmusNotAffected (rng ({(name\<^sub>F\<^sub>M\<^sub>U fmu)} -\<triangleleft> (fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I))))   (rng ({(name\<^sub>F\<^sub>M\<^sub>U fmu)} -\<triangleleft> (fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r NewI))))) \<and> ((mode\<^sub>F\<^sub>M\<^sub>U fmu) = FMUMode.U_EVENT )))
		 else
			undefined
		)
		)))))"

	
	
\<comment>\<open>VDM source: calculateOutput: (Importer * FMURef -> Importer)
	calculateOutput(I, equation) ==
let I1:Importer = getPort(I, equation) in updateEnvironmentEquation(I1, ((I.scenario).fmus)((equation.name)), equation)
	pre let fmu:FMU = ((I.scenario).fmus)((equation.name)) in ((equation in set ((I.activeEquations) \ (I.calculatedEquations))) and (((fmu.mode) = <EVENT>) and (pre_preGetI(I, fmu, (equation.ref)) and (preGetI(I, fmu, (equation.ref)) and (pre_getPort(I, equation) and pre_updateEnvironmentEquation(getPort(I, equation), ((I.scenario).fmus)((equation.name)), equation))))))
	post (pre_postVariableCalculation(equation, I, RESULT) and postVariableCalculation(equation, I, RESULT))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 873:5\<close>

\<comment>\<open>VDM source: pre_calculateOutput: (Importer * FMURef +> bool)
	pre_calculateOutput(I, equation) ==
let fmu:FMU = ((I.scenario).fmus)((equation.name)) in ((equation in set ((I.activeEquations) \ (I.calculatedEquations))) and (((fmu.mode) = <EVENT>) and (pre_preGetI(I, fmu, (equation.ref)) and (preGetI(I, fmu, (equation.ref)) and (pre_getPort(I, equation) and pre_updateEnvironmentEquation(getPort(I, equation), ((I.scenario).fmus)((equation.name)), equation))))))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 879:9\<close>
definition
	pre_calculateOutput :: "Importer \<Rightarrow> FMURef \<Rightarrow> bool"
where
	"pre_calculateOutput I   equation \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `pre_calculateOutput` specification.\<close>
		(inv_Importer I  \<and>  inv_FMURef equation)  \<and> 
		\<comment>\<open>User defined body of pre_calculateOutput.\<close>
		(
		let 
(fmu::FMU) = (the(((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) (name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f equation))))
		in
			(if (inv_FMU fmu) then
			((equation \<in> ((activeEquations\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I) - (calculatedEquations\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I))) \<and> (((mode\<^sub>F\<^sub>M\<^sub>U fmu) = FMUMode.U_EVENT ) \<and> ((pre_preGetI I   fmu   (ref\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f equation)) \<and> ((preGetI I   fmu   (ref\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f equation)) \<and> ((pre_getPort I   equation) \<and> (pre_updateEnvironmentEquation (getPort I   equation)   ((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) (name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f equation))   equation))))))
		 else
			undefined
		)
		)"


\<comment>\<open>VDM source: post_calculateOutput: (Importer * FMURef * Importer +> bool)
	post_calculateOutput(I, equation, RESULT) ==
(pre_postVariableCalculation(equation, I, RESULT) and postVariableCalculation(equation, I, RESULT))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 887:5\<close>
definition
	post_calculateOutput :: "Importer \<Rightarrow> FMURef \<Rightarrow> Importer \<Rightarrow> bool"
where
	"post_calculateOutput I   equation   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `post_calculateOutput` specification.\<close>
		(inv_Importer I  \<and>  inv_FMURef equation  \<and>  inv_Importer RESULT)  \<and> 
		\<comment>\<open>User defined body of post_calculateOutput.\<close>
		((pre_postVariableCalculation equation   I   RESULT) \<and> (postVariableCalculation equation   I   RESULT))"

definition
	calculateOutput :: "Importer \<Rightarrow> FMURef \<Rightarrow> Importer"
where
	"calculateOutput I   equation \<equiv> 
	\<comment>\<open>User defined body of calculateOutput.\<close>
	(
		let 
(I1::Importer) = (getPort I   equation)
		in
			(if (inv_Importer I1) then
			(updateEnvironmentEquation I1   ((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) (name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f equation))   equation)
		 else
			undefined
		)
		)"

	
	
\<comment>\<open>VDM source: assertFMUMode: (set of (FMU) * set1 of (FMUMode) -> bool)
	assertFMUMode(fmus, modes) ==
(exists1 mode in set modes & (forall fmu in set fmus & ((fmu.mode) = mode)))
	pre true\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 892:5\<close>

\<comment>\<open>VDM source: pre_assertFMUMode: (set of (FMU) * set1 of (FMUMode) +> bool)
	pre_assertFMUMode(fmus, modes) ==
true\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 896:9\<close>
definition
	pre_assertFMUMode :: "FMU VDMSet \<Rightarrow> FMUMode VDMSet1 \<Rightarrow> bool"
where
	"pre_assertFMUMode fmus   modes \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `pre_assertFMUMode` specification.\<close>
		((inv_VDMSet' inv_FMU  fmus)  \<and>  (inv_VDMSet1' (inv_FMUMode) modes))  \<and> 
		\<comment>\<open>User defined body of pre_assertFMUMode.\<close>
		(
		\<comment>\<open>Implicit union type parameters projection\<close>
		())"


\<comment>\<open>VDM source: post_assertFMUMode: (set of (FMU) * set1 of (FMUMode) * bool +> bool)
	post_assertFMUMode(fmus, modes, RESULT) ==
null\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 892:5\<close>
definition
	post_assertFMUMode :: "FMU VDMSet \<Rightarrow> FMUMode VDMSet1 \<Rightarrow> bool \<Rightarrow> bool"
where
	"post_assertFMUMode fmus   modes   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_assertFMUMode` specification.\<close>
		((inv_VDMSet' inv_FMU  fmus)  \<and>  (inv_VDMSet1' (inv_FMUMode) modes)  \<and>  (inv_bool RESULT))"

definition
	assertFMUMode :: "FMU VDMSet \<Rightarrow> FMUMode VDMSet1 \<Rightarrow> bool"
where
	"assertFMUMode fmus   modes \<equiv> 
	\<comment>\<open>User defined body of assertFMUMode.\<close>
	(
	\<comment>\<open>Implicit union type parameters projection\<close>
	())"

	
	
\<comment>\<open>VDM source: fmusSynchronized: (set1 of (FMU) -> bool)
	fmusSynchronized(fmus) ==
((card {(fmu.time) | fmu in set fmus}) = 1)
	pre true\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 899:5\<close>

\<comment>\<open>VDM source: pre_fmusSynchronized: (set1 of (FMU) +> bool)
	pre_fmusSynchronized(fmus) ==
true\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 902:9\<close>
definition
	pre_fmusSynchronized :: "FMU VDMSet1 \<Rightarrow> bool"
where
	"pre_fmusSynchronized fmus \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `pre_fmusSynchronized` specification.\<close>
		((inv_VDMSet1' inv_FMU  fmus))  \<and> 
		\<comment>\<open>User defined body of pre_fmusSynchronized.\<close>
		(True::\<bool>)"


\<comment>\<open>VDM source: post_fmusSynchronized: (set1 of (FMU) * bool +> bool)
	post_fmusSynchronized(fmus, RESULT) ==
null\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 899:5\<close>
definition
	post_fmusSynchronized :: "FMU VDMSet1 \<Rightarrow> bool \<Rightarrow> bool"
where
	"post_fmusSynchronized fmus   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_fmusSynchronized` specification.\<close>
		((inv_VDMSet1' inv_FMU  fmus)  \<and>  (inv_bool RESULT))"

definition
	fmusSynchronized :: "FMU VDMSet1 \<Rightarrow> bool"
where
	"fmusSynchronized fmus \<equiv> 
	\<comment>\<open>User defined body of fmusSynchronized.\<close>
	((vdm_card { (time\<^sub>F\<^sub>M\<^sub>U fmu) | fmu .  ((fmu \<in>fmus))  }) = (1::VDMNat1))"

	
	
\<comment>\<open>VDM source: fmusSynchronizedAtTime: (set1 of (FMU) * Time -> bool)
	fmusSynchronizedAtTime(fmus, t) ==
(fmusSynchronized(fmus) and (forall fmu in set fmus & ((fmu.time) = t)))
	pre pre_fmusSynchronized(fmus)\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 904:5\<close>

\<comment>\<open>VDM source: pre_fmusSynchronizedAtTime: (set1 of (FMU) * Time +> bool)
	pre_fmusSynchronizedAtTime(fmus, t) ==
pre_fmusSynchronized(fmus)\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 908:9\<close>
definition
	pre_fmusSynchronizedAtTime :: "FMU VDMSet1 \<Rightarrow> Time \<Rightarrow> bool"
where
	"pre_fmusSynchronizedAtTime fmus   t \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `pre_fmusSynchronizedAtTime` specification.\<close>
		((inv_VDMSet1' inv_FMU  fmus)  \<and>  inv_Time t)  \<and> 
		\<comment>\<open>User defined body of pre_fmusSynchronizedAtTime.\<close>
		(pre_fmusSynchronized fmus)"


\<comment>\<open>VDM source: post_fmusSynchronizedAtTime: (set1 of (FMU) * Time * bool +> bool)
	post_fmusSynchronizedAtTime(fmus, t, RESULT) ==
null\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 904:5\<close>
definition
	post_fmusSynchronizedAtTime :: "FMU VDMSet1 \<Rightarrow> Time \<Rightarrow> bool \<Rightarrow> bool"
where
	"post_fmusSynchronizedAtTime fmus   t   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_fmusSynchronizedAtTime` specification.\<close>
		((inv_VDMSet1' inv_FMU  fmus)  \<and>  inv_Time t  \<and>  (inv_bool RESULT))"

definition
	fmusSynchronizedAtTime :: "FMU VDMSet1 \<Rightarrow> Time \<Rightarrow> bool"
where
	"fmusSynchronizedAtTime fmus   t \<equiv> 
	\<comment>\<open>User defined body of fmusSynchronizedAtTime.\<close>
	((fmusSynchronized fmus) \<and> (\<forall> fmu \<in> fmus  . \<comment>\<open>Transform a VDM `=` expression into an `eq_Time` call\<close>
	(eq_Time (time\<^sub>F\<^sub>M\<^sub>U fmu)   t)))"

	
	
\<comment>\<open>VDM source: preInitialization: (Importer -> bool)
	preInitialization(I) ==
let fmus:set1 of (FMU) = (rng ((I.scenario).fmus)) in (pre_assertFMUMode(fmus, {<INIT>}) and (assertFMUMode(fmus, {<INIT>}) and (((I.time) = mk_Time(0, 0)) and (pre_fmusSynchronizedAtTime(fmus, (I.time)) and fmusSynchronizedAtTime(fmus, (I.time))))))
	pre true\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 911:5\<close>

\<comment>\<open>VDM source: pre_preInitialization: (Importer +> bool)
	pre_preInitialization(I) ==
true\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 919:9\<close>
definition
	pre_preInitialization :: "Importer \<Rightarrow> bool"
where
	"pre_preInitialization I \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `pre_preInitialization` specification.\<close>
		(inv_Importer I)  \<and> 
		\<comment>\<open>User defined body of pre_preInitialization.\<close>
		(True::\<bool>)"


\<comment>\<open>VDM source: post_preInitialization: (Importer * bool +> bool)
	post_preInitialization(I, RESULT) ==
null\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 911:5\<close>
definition
	post_preInitialization :: "Importer \<Rightarrow> bool \<Rightarrow> bool"
where
	"post_preInitialization I   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_preInitialization` specification.\<close>
		(inv_Importer I  \<and>  (inv_bool RESULT))"

definition
	preInitialization :: "Importer \<Rightarrow> bool"
where
	"preInitialization I \<equiv> 
	\<comment>\<open>User defined body of preInitialization.\<close>
	(
		let 
(fmus::FMU VDMSet1) = (rng (fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)))
		in
			(if ((inv_VDMSet1' inv_FMU  fmus)) then
			((pre_assertFMUMode fmus   {FMUMode.U_INIT }) \<and> ((assertFMUMode fmus   {FMUMode.U_INIT }) \<and> (\<comment>\<open>Transform a VDM `=` expression into an `eq_Time` call\<close>
	(eq_Time (time\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)   \<lparr>r\<^sub>T\<^sub>i\<^sub>m\<^sub>e = (0::VDMNat), i\<^sub>T\<^sub>i\<^sub>m\<^sub>e = (0::VDMNat)\<rparr>) \<and> ((pre_fmusSynchronizedAtTime fmus   (time\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) \<and> (fmusSynchronizedAtTime fmus   (time\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I))))))
		 else
			undefined
		)
		)"

	
	
\<comment>\<open>VDM source: filterOutputs: (seq of (FMU) * set of (PortType) -> set of (FMURef))
	filterOutputs(fmus, variableTypes) ==
(if (fmus = [])
then {}
else let fmu:FMU = (hd fmus) in ({mk_FMURef((fmu.name), (outputVar.ref)) | outputVar in set ((fmu.io).LFoutput) & ((outputVar.type) in set variableTypes)} union filterOutputs((tl fmus), variableTypes)))
	pre ((fmus <> []) => pre_filterOutputs((tl fmus), variableTypes))
	measure (len fmus)\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 924:5\<close>

\<comment>\<open>VDM source: pre_filterOutputs: (seq of (FMU) * set of (PortType) +> bool)
	pre_filterOutputs(fmus, variableTypes) ==
((fmus <> []) => pre_filterOutputs((tl fmus), variableTypes))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 932:20\<close>
definition
	pre_filterOutputs :: "FMU VDMSeq \<Rightarrow> PortType VDMSet \<Rightarrow> bool"
where
	"pre_filterOutputs fmus   variableTypes \<equiv> 
	\<comment>\<open>Implicitly defined type invariant checks for  `pre_filterOutputs` specification.\<close>
	((inv_VDMSeq' inv_FMU  fmus)  \<and>  (inv_VDMSet' (inv_PortType) variableTypes))  \<and> 
	\<comment>\<open>User defined body of pre_filterOutputs.\<close>
	(
	\<comment>\<open>Implicit union type parameters projection\<close>
	())"


\<comment>\<open>VDM source: post_filterOutputs: (seq of (FMU) * set of (PortType) * set of (FMURef) +> bool)
	post_filterOutputs(fmus, variableTypes, RESULT) ==
null\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 924:5\<close>
definition
	post_filterOutputs :: "FMU VDMSeq \<Rightarrow> PortType VDMSet \<Rightarrow> FMURef VDMSet \<Rightarrow> bool"
where
	"post_filterOutputs fmus   variableTypes   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_filterOutputs` specification.\<close>
		((inv_VDMSeq' inv_FMU  fmus)  \<and>  (inv_VDMSet' (inv_PortType) variableTypes)  \<and>  (inv_VDMSet' inv_FMURef  RESULT))"

fun
	filterOutputs :: "FMU VDMSeq \<Rightarrow> PortType VDMSet \<Rightarrow> FMURef VDMSet"
where
	"filterOutputs fmus   variableTypes = 
	\<comment>\<open>User defined body of filterOutputs.\<close>
	(
	\<comment>\<open>Implicit union type parameters projection\<close>
	())"

	
	
\<comment>\<open>VDM source: variablesSynchronized: (Scenario * set1 of (PortType) -> bool)
	variablesSynchronized(M, variableTypes) ==
let outputs:set of (FMURef) = filterOutputs([fmu | fmu in set (rng (M.fmus))], variableTypes) in (forall srcPort in set outputs & ((srcPort in set (dom ((M.connections).dataConnections))) and let trgPort:FMURef = ((M.connections).dataConnections)(srcPort) in (((M.fmus)((srcPort.name)).env)((srcPort.ref)) = ((M.fmus)((trgPort.name)).env)((trgPort.ref)))))
	pre pre_filterOutputs([fmu | fmu in set (rng (M.fmus))], variableTypes)\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 937:5\<close>

\<comment>\<open>VDM source: pre_variablesSynchronized: (Scenario * set1 of (PortType) +> bool)
	pre_variablesSynchronized(M, variableTypes) ==
pre_filterOutputs([fmu | fmu in set (rng (M.fmus))], variableTypes)\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 944:9\<close>
definition
	pre_variablesSynchronized :: "Scenario \<Rightarrow> PortType VDMSet1 \<Rightarrow> bool"
where
	"pre_variablesSynchronized M   variableTypes \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `pre_variablesSynchronized` specification.\<close>
		(inv_Scenario M  \<and>  (inv_VDMSet1' (inv_PortType) variableTypes))  \<and> 
		\<comment>\<open>User defined body of pre_variablesSynchronized.\<close>
		(
		\<comment>\<open>Implicit union type parameters projection\<close>
		())"


\<comment>\<open>VDM source: post_variablesSynchronized: (Scenario * set1 of (PortType) * bool +> bool)
	post_variablesSynchronized(M, variableTypes, RESULT) ==
null\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 937:5\<close>
definition
	post_variablesSynchronized :: "Scenario \<Rightarrow> PortType VDMSet1 \<Rightarrow> bool \<Rightarrow> bool"
where
	"post_variablesSynchronized M   variableTypes   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_variablesSynchronized` specification.\<close>
		(inv_Scenario M  \<and>  (inv_VDMSet1' (inv_PortType) variableTypes)  \<and>  (inv_bool RESULT))"

definition
	variablesSynchronized :: "Scenario \<Rightarrow> PortType VDMSet1 \<Rightarrow> bool"
where
	"variablesSynchronized M   variableTypes \<equiv> 
	\<comment>\<open>User defined body of variablesSynchronized.\<close>
	(
	\<comment>\<open>Implicit union type parameters projection\<close>
	())"

	
	
\<comment>\<open>VDM source: postInitialization: (Importer -> bool)
	postInitialization(I) ==
let fmus:set1 of (FMU) = (rng ((I.scenario).fmus)) in (pre_assertFMUMode(fmus, {<INIT>}) and (assertFMUMode(fmus, {<INIT>}) and (pre_fmusSynchronizedAtTime(fmus, (I.time)) and (fmusSynchronizedAtTime(fmus, (I.time)) and (((I.time) = mk_Time(0, 0)) and variablesSynchronized((I.scenario), {<continous>, <discrete>}))))))
	pre pre_variablesSynchronized((I.scenario), {<continous>, <discrete>})\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 947:5\<close>

\<comment>\<open>VDM source: pre_postInitialization: (Importer +> bool)
	pre_postInitialization(I) ==
pre_variablesSynchronized((I.scenario), {<continous>, <discrete>})\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 956:9\<close>
definition
	pre_postInitialization :: "Importer \<Rightarrow> bool"
where
	"pre_postInitialization I \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `pre_postInitialization` specification.\<close>
		(inv_Importer I)  \<and> 
		\<comment>\<open>User defined body of pre_postInitialization.\<close>
		(pre_variablesSynchronized (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)   {PortType.U_continous  , PortType.U_discrete })"


\<comment>\<open>VDM source: post_postInitialization: (Importer * bool +> bool)
	post_postInitialization(I, RESULT) ==
null\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 947:5\<close>
definition
	post_postInitialization :: "Importer \<Rightarrow> bool \<Rightarrow> bool"
where
	"post_postInitialization I   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_postInitialization` specification.\<close>
		(inv_Importer I  \<and>  (inv_bool RESULT))"

definition
	postInitialization :: "Importer \<Rightarrow> bool"
where
	"postInitialization I \<equiv> 
	\<comment>\<open>User defined body of postInitialization.\<close>
	(
		let 
(fmus::FMU VDMSet1) = (rng (fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)))
		in
			(if ((inv_VDMSet1' inv_FMU  fmus)) then
			((pre_assertFMUMode fmus   {FMUMode.U_INIT }) \<and> ((assertFMUMode fmus   {FMUMode.U_INIT }) \<and> ((pre_fmusSynchronizedAtTime fmus   (time\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) \<and> ((fmusSynchronizedAtTime fmus   (time\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) \<and> (\<comment>\<open>Transform a VDM `=` expression into an `eq_Time` call\<close>
	(eq_Time (time\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)   \<lparr>r\<^sub>T\<^sub>i\<^sub>m\<^sub>e = (0::VDMNat), i\<^sub>T\<^sub>i\<^sub>m\<^sub>e = (0::VDMNat)\<rparr>) \<and> (variablesSynchronized (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)   {PortType.U_continous  , PortType.U_discrete }))))))
		 else
			undefined
		)
		)"

	
	
\<comment>\<open>VDM source: preStepI: (Importer * FMU -> bool)
	preStepI(I, fmu) ==
(not (exists [m in set (rng ((I.scenario).fmus))] & (((m.name) <> (fmu.name)) and (((m.time) < (fmu.time)) and preStepT(fmu, (I.stepSize))))))
	pre pre_preStepT(fmu, (I.stepSize))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 959:5\<close>

\<comment>\<open>VDM source: pre_preStepI: (Importer * FMU +> bool)
	pre_preStepI(I, fmu) ==
pre_preStepT(fmu, (I.stepSize))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 964:9\<close>
definition
	pre_preStepI :: "Importer \<Rightarrow> FMU \<Rightarrow> bool"
where
	"pre_preStepI I   fmu \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `pre_preStepI` specification.\<close>
		(inv_Importer I  \<and>  inv_FMU fmu)  \<and> 
		\<comment>\<open>User defined body of pre_preStepI.\<close>
		(pre_preStepT fmu   (stepSize\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I))"


\<comment>\<open>VDM source: post_preStepI: (Importer * FMU * bool +> bool)
	post_preStepI(I, fmu, RESULT) ==
null\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 959:5\<close>
definition
	post_preStepI :: "Importer \<Rightarrow> FMU \<Rightarrow> bool \<Rightarrow> bool"
where
	"post_preStepI I   fmu   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_preStepI` specification.\<close>
		(inv_Importer I  \<and>  inv_FMU fmu  \<and>  (inv_bool RESULT))"

definition
	preStepI :: "Importer \<Rightarrow> FMU \<Rightarrow> bool"
where
	"preStepI I   fmu \<equiv> 
	\<comment>\<open>User defined body of preStepI.\<close>
	(\<not> (\<exists> m \<in> (rng (fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)))  . (((name\<^sub>F\<^sub>M\<^sub>U m) \<noteq> (name\<^sub>F\<^sub>M\<^sub>U fmu)) \<and> (\<comment>\<open>Transform a VDM `<` expression into an `ord_Time` call\<close>
	(ord_Time (time\<^sub>F\<^sub>M\<^sub>U m)   (time\<^sub>F\<^sub>M\<^sub>U fmu)) \<and> (preStepT fmu   (stepSize\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I))))))"

	
	
\<comment>\<open>VDM source: ImporterNotAffected: (Importer * Importer -> bool)
	ImporterNotAffected(oldImporter, newImporter) ==
(((oldImporter.activeClocks) = (newImporter.activeClocks)) and (((oldImporter.readyClocks) = (newImporter.readyClocks)) and (((oldImporter.inactiveClocks) = (newImporter.inactiveClocks)) and (((oldImporter.relevantOutputClocks) = (newImporter.relevantOutputClocks)) and (((oldImporter.relevantInputClocks) = (newImporter.relevantInputClocks)) and (((oldImporter.activeEquations) = (newImporter.activeEquations)) and (((oldImporter.calculatedEquations) = (newImporter.calculatedEquations)) and (((oldImporter.readyEquations) = (newImporter.readyEquations)) and (((oldImporter.endtime) = (newImporter.endtime)) and ((oldImporter.valueMap) = (newImporter.valueMap)))))))))))
	pre true\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 966:5\<close>

\<comment>\<open>VDM source: pre_ImporterNotAffected: (Importer * Importer +> bool)
	pre_ImporterNotAffected(oldImporter, newImporter) ==
true\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 978:9\<close>
definition
	pre_ImporterNotAffected :: "Importer \<Rightarrow> Importer \<Rightarrow> bool"
where
	"pre_ImporterNotAffected oldImporter   newImporter \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `pre_ImporterNotAffected` specification.\<close>
		(inv_Importer oldImporter  \<and>  inv_Importer newImporter)  \<and> 
		\<comment>\<open>User defined body of pre_ImporterNotAffected.\<close>
		(True::\<bool>)"


\<comment>\<open>VDM source: post_ImporterNotAffected: (Importer * Importer * bool +> bool)
	post_ImporterNotAffected(oldImporter, newImporter, RESULT) ==
null\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 966:5\<close>
definition
	post_ImporterNotAffected :: "Importer \<Rightarrow> Importer \<Rightarrow> bool \<Rightarrow> bool"
where
	"post_ImporterNotAffected oldImporter   newImporter   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_ImporterNotAffected` specification.\<close>
		(inv_Importer oldImporter  \<and>  inv_Importer newImporter  \<and>  (inv_bool RESULT))"

definition
	ImporterNotAffected :: "Importer \<Rightarrow> Importer \<Rightarrow> bool"
where
	"ImporterNotAffected oldImporter   newImporter \<equiv> 
	\<comment>\<open>User defined body of ImporterNotAffected.\<close>
	(((activeClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r oldImporter) = (activeClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r newImporter)) \<and> (((readyClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r oldImporter) = (readyClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r newImporter)) \<and> (((inactiveClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r oldImporter) = (inactiveClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r newImporter)) \<and> (((relevantOutputClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r oldImporter) = (relevantOutputClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r newImporter)) \<and> (((relevantInputClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r oldImporter) = (relevantInputClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r newImporter)) \<and> (((activeEquations\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r oldImporter) = (activeEquations\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r newImporter)) \<and> (((calculatedEquations\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r oldImporter) = (calculatedEquations\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r newImporter)) \<and> (((readyEquations\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r oldImporter) = (readyEquations\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r newImporter)) \<and> (\<comment>\<open>Transform a VDM `=` expression into an `eq_Time` call\<close>
	(eq_Time (endtime\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r oldImporter)   (endtime\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r newImporter)) \<and> ((valueMap\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r oldImporter) = (valueMap\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r newImporter)))))))))))"

	
	
\<comment>\<open>VDM source: stepFMU: (Importer * FMU -> Importer)
	stepFMU(I, fmu) ==
let mk_(fmuUpdated, step, event):(FMU * Real1 * bool) = step_tm(fmu, (I.stepSize)) in mu(I, scenario |-> mu((I.scenario), fmus |-> (((I.scenario).fmus) ++ {(fmuUpdated.name) |-> fmuUpdated})), fmusWithEvent |-> (if event
then ((I.fmusWithEvent) union {(fmu.name)})
else (I.fmusWithEvent)), stepSize |-> step)
	pre (pre_preStepI(I, fmu) and (preStepI(I, fmu) and pre_step_tm(fmu, (I.stepSize))))
	post let resultFMUs:set of (FMU) = (rng ({(fmu.name)} <-: ((RESULT.scenario).fmus))), oldFMUs:set of (FMU) = (rng ({(fmu.name)} <-: ((I.scenario).fmus))) in (pre_fmusNotAffected(oldFMUs, resultFMUs) and (fmusNotAffected(oldFMUs, resultFMUs) and (((I.fmusWithEvent) subset (RESULT.fmusWithEvent)) and (((I.stepSize) >= (RESULT.stepSize)) and (pre_ImporterNotAffected(I, RESULT) and ImporterNotAffected(I, RESULT))))))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 985:5\<close>

\<comment>\<open>VDM source: pre_stepFMU: (Importer * FMU +> bool)
	pre_stepFMU(I, fmu) ==
(pre_preStepI(I, fmu) and (preStepI(I, fmu) and pre_step_tm(fmu, (I.stepSize))))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 995:9\<close>
definition
	pre_stepFMU :: "Importer \<Rightarrow> FMU \<Rightarrow> bool"
where
	"pre_stepFMU I   fmu \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `pre_stepFMU` specification.\<close>
		(inv_Importer I  \<and>  inv_FMU fmu)  \<and> 
		\<comment>\<open>User defined body of pre_stepFMU.\<close>
		((pre_preStepI I   fmu) \<and> ((preStepI I   fmu) \<and> (pre_step_tm fmu   (stepSize\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I))))"


\<comment>\<open>VDM source: post_stepFMU: (Importer * FMU * Importer +> bool)
	post_stepFMU(I, fmu, RESULT) ==
let resultFMUs:set of (FMU) = (rng ({(fmu.name)} <-: ((RESULT.scenario).fmus))), oldFMUs:set of (FMU) = (rng ({(fmu.name)} <-: ((I.scenario).fmus))) in (pre_fmusNotAffected(oldFMUs, resultFMUs) and (fmusNotAffected(oldFMUs, resultFMUs) and (((I.fmusWithEvent) subset (RESULT.fmusWithEvent)) and (((I.stepSize) >= (RESULT.stepSize)) and (pre_ImporterNotAffected(I, RESULT) and ImporterNotAffected(I, RESULT))))))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 998:9\<close>
definition
	post_stepFMU :: "Importer \<Rightarrow> FMU \<Rightarrow> Importer \<Rightarrow> bool"
where
	"post_stepFMU I   fmu   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `post_stepFMU` specification.\<close>
		(inv_Importer I  \<and>  inv_FMU fmu  \<and>  inv_Importer RESULT)  \<and> 
		\<comment>\<open>User defined body of post_stepFMU.\<close>
		(
		let 
(resultFMUs::FMU VDMSet) = (rng ({(name\<^sub>F\<^sub>M\<^sub>U fmu)} -\<triangleleft> (fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r RESULT))))
		;
		
(oldFMUs::FMU VDMSet) = (rng ({(name\<^sub>F\<^sub>M\<^sub>U fmu)} -\<triangleleft> (fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I))))
		in
			(if ((inv_VDMSet' inv_FMU  resultFMUs))
	 \<and> 
	((inv_VDMSet' inv_FMU  oldFMUs)) then
			((pre_fmusNotAffected oldFMUs   resultFMUs) \<and> ((fmusNotAffected oldFMUs   resultFMUs) \<and> (((fmusWithEvent\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I) \<subseteq> (fmusWithEvent\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r RESULT)) \<and> (((stepSize\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I) \<ge> (stepSize\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r RESULT)) \<and> ((pre_ImporterNotAffected I   RESULT) \<and> (ImporterNotAffected I   RESULT))))))
		 else
			undefined
		)
		)"

definition
	stepFMU :: "Importer \<Rightarrow> FMU \<Rightarrow> Importer"
where
	"stepFMU I   fmu \<equiv> 
	\<comment>\<open>User defined body of stepFMU.\<close>
	(
		let 
(fmuUpdated::FMU) = (step_tm fmu   (stepSize\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I));
(event::bool) = (step_tm fmu   (stepSize\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I));
(step::Real1) = (step_tm fmu   (stepSize\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I))
		in
			(if (
		( (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U (fst dummy0)))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U (fst dummy0))))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U (fst dummy0)))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U (fst dummy0))))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U (fst dummy0)))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U (fst dummy0)))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U (fst dummy0)))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U (fst dummy0))))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U (fst dummy0)))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U (fst dummy0))))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U (fst dummy0))))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U (fst dummy0)))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U (fst dummy0)))) )\<and>
		 ((inv_VDMReal (fst (snd dummy0))))\<and>
		 (inv_bool (snd (snd dummy0)))
		)) then
			(I)\<lparr>scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r := ((scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I))\<lparr>fmus\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r := ((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) \<dagger> [(name\<^sub>F\<^sub>M\<^sub>U fmuUpdated)\<mapsto>fmuUpdated])\<rparr>, fmusWithEvent\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r := (
		if (event) then
		(((fmusWithEvent\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I) \<union> {(name\<^sub>F\<^sub>M\<^sub>U fmu)}))
		else
		((fmusWithEvent\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I))), stepSize\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r := step\<rparr>
		 else
			undefined
		)
		)"

	
	
\<comment>\<open>VDM source: setClock: (Importer * FMU * Ref * bool -> Importer)
	setClock(I, fmu, clock, val) ==
let fmuUpdated:FMU = set_cm(fmu, clock, val), fmuref:FMURef = mk_FMURef((fmu.name), clock), feedthroughClocks:set of (FMURef) = {mk_FMURef((fmu.name), (c.ref)) | c in set (fmu.clocks) & (clock in set (c.dependsOn))}, I1:Importer = mu(I, valueMap |-> ({fmuref} <-: (I.valueMap)), relevantInputClocks |-> ((I.relevantInputClocks) \ {fmuref}), relevantOutputClocks |-> ((I.relevantOutputClocks) union feedthroughClocks)) in updateEnvironmentClock(I1, fmuUpdated, clock, val)
	pre (pre_set_cm(fmu, clock, val) and let fmuRef:FMURef = mk_FMURef((fmu.name), clock) in ((fmuRef in set (I.relevantInputClocks)) and ((val <=> (fmuRef in set ((I.inactiveClocks) inter (I.readyClocks)))) and ((fmu.mode) = <EVENT>))))
	post let fmuRef:FMURef = mk_FMURef((fmu.name), clock) in ((fmuRef not in set (RESULT.relevantInputClocks)) and (((card (RESULT.relevantInputClocks)) < (card (I.relevantInputClocks))) and (((((RESULT.scenario).fmus)((fmu.name)).mode) = <EVENT>) and (val <=> ((fmuRef in set (RESULT.activeClocks)) and (fmuRef not in set ((RESULT.readyClocks) union (RESULT.inactiveClocks))))))))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1011:5\<close>

\<comment>\<open>VDM source: pre_setClock: (Importer * FMU * Ref * bool +> bool)
	pre_setClock(I, fmu, clock, val) ==
(pre_set_cm(fmu, clock, val) and let fmuRef:FMURef = mk_FMURef((fmu.name), clock) in ((fmuRef in set (I.relevantInputClocks)) and ((val <=> (fmuRef in set ((I.inactiveClocks) inter (I.readyClocks)))) and ((fmu.mode) = <EVENT>))))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1024:9\<close>
definition
	pre_setClock :: "Importer \<Rightarrow> FMU \<Rightarrow> Ref \<Rightarrow> bool \<Rightarrow> bool"
where
	"pre_setClock I   fmu   clock   val \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `pre_setClock` specification.\<close>
		(inv_Importer I  \<and>  inv_FMU fmu  \<and>  (inv_Ref clock)  \<and>  (inv_bool val))  \<and> 
		\<comment>\<open>User defined body of pre_setClock.\<close>
		((pre_set_cm fmu   clock   val) \<and> (
		let 
(fmuRef::FMURef) = \<lparr>name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f = (name\<^sub>F\<^sub>M\<^sub>U fmu), ref\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f = clock\<rparr>
		in
			(if (inv_FMURef fmuRef) then
			((fmuRef \<in> (relevantInputClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) \<and> ((val \<longleftrightarrow> (fmuRef \<in> ((inactiveClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I) \<inter> (readyClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)))) \<and> ((mode\<^sub>F\<^sub>M\<^sub>U fmu) = FMUMode.U_EVENT )))
		 else
			undefined
		)
		))"


\<comment>\<open>VDM source: post_setClock: (Importer * FMU * Ref * bool * Importer +> bool)
	post_setClock(I, fmu, clock, val, RESULT) ==
let fmuRef:FMURef = mk_FMURef((fmu.name), clock) in ((fmuRef not in set (RESULT.relevantInputClocks)) and (((card (RESULT.relevantInputClocks)) < (card (I.relevantInputClocks))) and (((((RESULT.scenario).fmus)((fmu.name)).mode) = <EVENT>) and (val <=> ((fmuRef in set (RESULT.activeClocks)) and (fmuRef not in set ((RESULT.readyClocks) union (RESULT.inactiveClocks))))))))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1030:9\<close>
definition
	post_setClock :: "Importer \<Rightarrow> FMU \<Rightarrow> Ref \<Rightarrow> bool \<Rightarrow> Importer \<Rightarrow> bool"
where
	"post_setClock I   fmu   clock   val   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `post_setClock` specification.\<close>
		(inv_Importer I  \<and>  inv_FMU fmu  \<and>  (inv_Ref clock)  \<and>  (inv_bool val)  \<and>  inv_Importer RESULT)  \<and> 
		\<comment>\<open>User defined body of post_setClock.\<close>
		(
		let 
(fmuRef::FMURef) = \<lparr>name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f = (name\<^sub>F\<^sub>M\<^sub>U fmu), ref\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f = clock\<rparr>
		in
			(if (inv_FMURef fmuRef) then
			((fmuRef \<notin> (relevantInputClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r RESULT)) \<and> (((vdm_card (relevantInputClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r RESULT)) < (vdm_card (relevantInputClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I))) \<and> (((mode\<^sub>F\<^sub>M\<^sub>U (the(((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r RESULT)) (name\<^sub>F\<^sub>M\<^sub>U fmu))))) = FMUMode.U_EVENT ) \<and> (val \<longleftrightarrow> ((fmuRef \<in> (activeClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r RESULT)) \<and> (fmuRef \<notin> ((readyClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r RESULT) \<union> (inactiveClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r RESULT))))))))
		 else
			undefined
		)
		)"

definition
	setClock :: "Importer \<Rightarrow> FMU \<Rightarrow> Ref \<Rightarrow> bool \<Rightarrow> Importer"
where
	"setClock I   fmu   clock   val \<equiv> 
	\<comment>\<open>User defined body of setClock.\<close>
	(
		let 
(fmuUpdated::FMU) = (set_cm fmu   clock   val)
		;
		
(fmuref::FMURef) = \<lparr>name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f = (name\<^sub>F\<^sub>M\<^sub>U fmu), ref\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f = clock\<rparr>
		;
		
(feedthroughClocks::FMURef VDMSet) = { \<lparr>name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f = (name\<^sub>F\<^sub>M\<^sub>U fmu), ref\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f = (ref\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k c)\<rparr> | c .  ((c \<in>(clocks\<^sub>F\<^sub>M\<^sub>U fmu)))  \<and> (clock \<in> (dependsOn\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k c)) }
		;
		
(I1::Importer) = (I)\<lparr>valueMap\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r := ({fmuref} -\<triangleleft> (valueMap\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)), relevantInputClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r := ((relevantInputClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I) - {fmuref}), relevantOutputClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r := ((relevantOutputClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I) \<union> feedthroughClocks)\<rparr>
		in
			(if (inv_FMU fmuUpdated)
	 \<and> 
	(inv_FMURef fmuref)
	 \<and> 
	((inv_VDMSet' inv_FMURef  feedthroughClocks))
	 \<and> 
	(inv_Importer I1) then
			(updateEnvironmentClock I1   fmuUpdated   clock   val)
		 else
			undefined
		)
		)"

	
	
\<comment>\<open>VDM source: preGetCI: (Importer * FMU * Ref -> bool)
	preGetCI(I, fmu, clock) ==
let outputVar:FMURef = mk_FMURef((fmu.name), clock) in ((outputVar in set (I.relevantOutputClocks)) and preGetC(fmu, clock))
	pre pre_preGetC(fmu, clock)\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1038:5\<close>

\<comment>\<open>VDM source: pre_preGetCI: (Importer * FMU * Ref +> bool)
	pre_preGetCI(I, fmu, clock) ==
pre_preGetC(fmu, clock)\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1043:9\<close>
definition
	pre_preGetCI :: "Importer \<Rightarrow> FMU \<Rightarrow> Ref \<Rightarrow> bool"
where
	"pre_preGetCI I   fmu   clock \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `pre_preGetCI` specification.\<close>
		(inv_Importer I  \<and>  inv_FMU fmu  \<and>  (inv_Ref clock))  \<and> 
		\<comment>\<open>User defined body of pre_preGetCI.\<close>
		(pre_preGetC fmu   clock)"


\<comment>\<open>VDM source: post_preGetCI: (Importer * FMU * Ref * bool +> bool)
	post_preGetCI(I, fmu, clock, RESULT) ==
null\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1038:5\<close>
definition
	post_preGetCI :: "Importer \<Rightarrow> FMU \<Rightarrow> Ref \<Rightarrow> bool \<Rightarrow> bool"
where
	"post_preGetCI I   fmu   clock   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_preGetCI` specification.\<close>
		(inv_Importer I  \<and>  inv_FMU fmu  \<and>  (inv_Ref clock)  \<and>  (inv_bool RESULT))"

definition
	preGetCI :: "Importer \<Rightarrow> FMU \<Rightarrow> Ref \<Rightarrow> bool"
where
	"preGetCI I   fmu   clock \<equiv> 
	\<comment>\<open>User defined body of preGetCI.\<close>
	(
		let 
(outputVar::FMURef) = \<lparr>name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f = (name\<^sub>F\<^sub>M\<^sub>U fmu), ref\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f = clock\<rparr>
		in
			(if (inv_FMURef outputVar) then
			((outputVar \<in> (relevantOutputClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) \<and> (preGetC fmu   clock))
		 else
			undefined
		)
		)"

	
	
\<comment>\<open>VDM source: preSetCI: (Importer * FMU * Ref -> bool)
	preSetCI(I, fmu, clock) ==
let inputVar:FMURef = mk_FMURef((fmu.name), clock) in ((inputVar in set ((dom (I.valueMap)) inter (I.relevantInputClocks))) and let val:FMIValue = (I.valueMap)(inputVar) in (pre_preSetC(fmu, clock, (val.fmiValue)) and (preSetC(fmu, clock, (val.fmiValue)) and ((val.fmiValue) <=> (inputVar in set ((I.inactiveClocks) inter (I.readyClocks)))))))
	pre true\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1045:5\<close>

\<comment>\<open>VDM source: pre_preSetCI: (Importer * FMU * Ref +> bool)
	pre_preSetCI(I, fmu, clock) ==
true\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1053:9\<close>
definition
	pre_preSetCI :: "Importer \<Rightarrow> FMU \<Rightarrow> Ref \<Rightarrow> bool"
where
	"pre_preSetCI I   fmu   clock \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `pre_preSetCI` specification.\<close>
		(inv_Importer I  \<and>  inv_FMU fmu  \<and>  (inv_Ref clock))  \<and> 
		\<comment>\<open>User defined body of pre_preSetCI.\<close>
		(True::\<bool>)"


\<comment>\<open>VDM source: post_preSetCI: (Importer * FMU * Ref * bool +> bool)
	post_preSetCI(I, fmu, clock, RESULT) ==
null\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1045:5\<close>
definition
	post_preSetCI :: "Importer \<Rightarrow> FMU \<Rightarrow> Ref \<Rightarrow> bool \<Rightarrow> bool"
where
	"post_preSetCI I   fmu   clock   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_preSetCI` specification.\<close>
		(inv_Importer I  \<and>  inv_FMU fmu  \<and>  (inv_Ref clock)  \<and>  (inv_bool RESULT))"

definition
	preSetCI :: "Importer \<Rightarrow> FMU \<Rightarrow> Ref \<Rightarrow> bool"
where
	"preSetCI I   fmu   clock \<equiv> 
	\<comment>\<open>User defined body of preSetCI.\<close>
	(
		let 
(inputVar::FMURef) = \<lparr>name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f = (name\<^sub>F\<^sub>M\<^sub>U fmu), ref\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f = clock\<rparr>
		in
			(if (inv_FMURef inputVar) then
			((inputVar \<in> ((dom (valueMap\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) \<inter> (relevantInputClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I))) \<and> (
		let 
(val::FMIValue) = (the(((valueMap\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I) inputVar)))
		in
			(if (inv_FMIValue val) then
			((pre_preSetC fmu   clock   (fmiValue\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e val)) \<and> ((preSetC fmu   clock   (fmiValue\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e val)) \<and> ((fmiValue\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e val) \<longleftrightarrow> (inputVar \<in> ((inactiveClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I) \<inter> (readyClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I))))))
		 else
			undefined
		)
		))
		 else
			undefined
		)
		)"

	
	
\<comment>\<open>VDM source: queryClock: (Importer * FMU * Ref -> Importer)
	queryClock(I, fmu, clock) ==
let mk_(fmuUpdated, val):(FMU * FMIValue) = get_cm(fmu, clock), fmuref:FMURef = mk_FMURef((fmu.name), clock), connectedClock:FMURef = (((I.scenario).connections).clockConnections)(fmuref), I1:Importer = mu(I, valueMap |-> ((I.valueMap) ++ {connectedClock |-> val}), relevantOutputClocks |-> ((I.relevantOutputClocks) \ {fmuref}), relevantInputClocks |-> ((I.relevantInputClocks) union {connectedClock})) in updateEnvironmentClock(I1, fmuUpdated, clock, (val.fmiValue))
	pre ((mk_FMURef((fmu.name), clock) in set (I.relevantOutputClocks)) and ((clock in set {(c.ref) | c in set (fmu.clocks) & ((c.type) = <output>)}) and (pre_preGetCI(I, fmu, clock) and (preGetCI(I, fmu, clock) and (pre_get_cm(fmu, clock) and let mk_(fmuUpdated, val):(FMU * FMIValue) = get_cm(fmu, clock), fmuref:FMURef = mk_FMURef((fmu.name), clock), connectedClock:FMURef = (((I.scenario).connections).clockConnections)(fmuref), I1:Importer = mu(I, valueMap |-> ((I.valueMap) ++ {connectedClock |-> val}), relevantOutputClocks |-> ((I.relevantOutputClocks) \ {fmuref}), relevantInputClocks |-> ((I.relevantInputClocks) union {connectedClock})) in pre_updateEnvironmentClock(I1, fmuUpdated, clock, (val.fmiValue)))))))
	post (mk_FMURef((fmu.name), clock) not in set (RESULT.relevantOutputClocks))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1058:5\<close>

\<comment>\<open>VDM source: pre_queryClock: (Importer * FMU * Ref +> bool)
	pre_queryClock(I, fmu, clock) ==
((mk_FMURef((fmu.name), clock) in set (I.relevantOutputClocks)) and ((clock in set {(c.ref) | c in set (fmu.clocks) & ((c.type) = <output>)}) and (pre_preGetCI(I, fmu, clock) and (preGetCI(I, fmu, clock) and (pre_get_cm(fmu, clock) and let mk_(fmuUpdated, val):(FMU * FMIValue) = get_cm(fmu, clock), fmuref:FMURef = mk_FMURef((fmu.name), clock), connectedClock:FMURef = (((I.scenario).connections).clockConnections)(fmuref), I1:Importer = mu(I, valueMap |-> ((I.valueMap) ++ {connectedClock |-> val}), relevantOutputClocks |-> ((I.relevantOutputClocks) \ {fmuref}), relevantInputClocks |-> ((I.relevantInputClocks) union {connectedClock})) in pre_updateEnvironmentClock(I1, fmuUpdated, clock, (val.fmiValue)))))))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1071:9\<close>
definition
	pre_queryClock :: "Importer \<Rightarrow> FMU \<Rightarrow> Ref \<Rightarrow> bool"
where
	"pre_queryClock I   fmu   clock \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `pre_queryClock` specification.\<close>
		(inv_Importer I  \<and>  inv_FMU fmu  \<and>  (inv_Ref clock))  \<and> 
		\<comment>\<open>User defined body of pre_queryClock.\<close>
		((\<lparr>name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f = (name\<^sub>F\<^sub>M\<^sub>U fmu), ref\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f = clock\<rparr> \<in> (relevantOutputClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) \<and> ((clock \<in> { (ref\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k c) | c .  ((c \<in>(clocks\<^sub>F\<^sub>M\<^sub>U fmu)))  \<and> ((type\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k c) = Causality.U_output ) }) \<and> ((pre_preGetCI I   fmu   clock) \<and> ((preGetCI I   fmu   clock) \<and> ((pre_get_cm fmu   clock) \<and> (
		let 
(fmuUpdated::FMU) = (get_cm fmu   clock);
(val::FMIValue) = (get_cm fmu   clock)
		;
		
(fmuref::FMURef) = \<lparr>name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f = (name\<^sub>F\<^sub>M\<^sub>U fmu), ref\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f = clock\<rparr>
		;
		
(connectedClock::FMURef) = (the(((clockConnections\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o\<^sub>C\<^sub>o\<^sub>n\<^sub>n\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n\<^sub>s (connections\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I))) fmuref)))
		;
		
(I1::Importer) = (I)\<lparr>valueMap\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r := ((valueMap\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I) \<dagger> [connectedClock\<mapsto>val]), relevantOutputClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r := ((relevantOutputClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I) - {fmuref}), relevantInputClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r := ((relevantInputClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I) \<union> {connectedClock})\<rparr>
		in
			(if (
		( (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U (fst dummy0)))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U (fst dummy0))))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U (fst dummy0)))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U (fst dummy0))))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U (fst dummy0)))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U (fst dummy0)))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U (fst dummy0)))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U (fst dummy0))))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U (fst dummy0)))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U (fst dummy0))))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U (fst dummy0))))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U (fst dummy0)))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U (fst dummy0)))) )\<and>
		  ((((case (fmiValue\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e (snd dummy0)) of
		 ValueType.U_bool (fmiValue\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e (snd dummy0)) \<Rightarrow> (inv_bool (fmiValue\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e (snd dummy0)))
		  | ValueType.U_VDMReal (fmiValue\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e (snd dummy0)) \<Rightarrow> (inv_VDMReal (fmiValue\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e (snd dummy0)))
		 ))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e (snd dummy0)))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e (snd dummy0))))) )) )
		))
	 \<and> 
	(inv_FMURef fmuref)
	 \<and> 
	(inv_FMURef connectedClock)
	 \<and> 
	(inv_Importer I1) then
			(pre_updateEnvironmentClock I1   fmuUpdated   clock   (fmiValue\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e val))
		 else
			undefined
		)
		))))))"


\<comment>\<open>VDM source: post_queryClock: (Importer * FMU * Ref * Importer +> bool)
	post_queryClock(I, fmu, clock, RESULT) ==
(mk_FMURef((fmu.name), clock) not in set (RESULT.relevantOutputClocks))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1085:36\<close>
definition
	post_queryClock :: "Importer \<Rightarrow> FMU \<Rightarrow> Ref \<Rightarrow> Importer \<Rightarrow> bool"
where
	"post_queryClock I   fmu   clock   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `post_queryClock` specification.\<close>
		(inv_Importer I  \<and>  inv_FMU fmu  \<and>  (inv_Ref clock)  \<and>  inv_Importer RESULT)  \<and> 
		\<comment>\<open>User defined body of post_queryClock.\<close>
		(\<lparr>name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f = (name\<^sub>F\<^sub>M\<^sub>U fmu), ref\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f = clock\<rparr> \<notin> (relevantOutputClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r RESULT))"

definition
	queryClock :: "Importer \<Rightarrow> FMU \<Rightarrow> Ref \<Rightarrow> Importer"
where
	"queryClock I   fmu   clock \<equiv> 
	\<comment>\<open>User defined body of queryClock.\<close>
	(
		let 
(fmuUpdated::FMU) = (get_cm fmu   clock);
(val::FMIValue) = (get_cm fmu   clock)
		;
		
(fmuref::FMURef) = \<lparr>name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f = (name\<^sub>F\<^sub>M\<^sub>U fmu), ref\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f = clock\<rparr>
		;
		
(connectedClock::FMURef) = (the(((clockConnections\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o\<^sub>C\<^sub>o\<^sub>n\<^sub>n\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n\<^sub>s (connections\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I))) fmuref)))
		;
		
(I1::Importer) = (I)\<lparr>valueMap\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r := ((valueMap\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I) \<dagger> [connectedClock\<mapsto>val]), relevantOutputClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r := ((relevantOutputClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I) - {fmuref}), relevantInputClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r := ((relevantInputClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I) \<union> {connectedClock})\<rparr>
		in
			(if (
		( (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U (fst dummy0)))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U (fst dummy0))))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U (fst dummy0)))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U (fst dummy0))))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U (fst dummy0)))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U (fst dummy0)))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U (fst dummy0)))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U (fst dummy0))))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U (fst dummy0)))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U (fst dummy0))))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U (fst dummy0))))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U (fst dummy0)))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U (fst dummy0)))) )\<and>
		  ((((case (fmiValue\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e (snd dummy0)) of
		 ValueType.U_bool (fmiValue\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e (snd dummy0)) \<Rightarrow> (inv_bool (fmiValue\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e (snd dummy0)))
		  | ValueType.U_VDMReal (fmiValue\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e (snd dummy0)) \<Rightarrow> (inv_VDMReal (fmiValue\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e (snd dummy0)))
		 ))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e (snd dummy0)))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e (snd dummy0))))) )) )
		))
	 \<and> 
	(inv_FMURef fmuref)
	 \<and> 
	(inv_FMURef connectedClock)
	 \<and> 
	(inv_Importer I1) then
			(updateEnvironmentClock I1   fmuUpdated   clock   (fmiValue\<^sub>F\<^sub>M\<^sub>I\<^sub>V\<^sub>a\<^sub>l\<^sub>u\<^sub>e val))
		 else
			undefined
		)
		)"

	
	
\<comment>\<open>VDM source: runAction: (Importer * Action -> Importer)
	runAction(I, action) ==
let fmus:map (Name) to (FMU) = ((I.scenario).fmus), mk_Action(actionType, fmu, port):Action = action in (cases actionType :
<get> -> (if ((fmus(fmu).mode) = <EVENT>)
then calculateOutput(I, mk_FMURef(fmu, port))
else getPort(I, mk_FMURef(fmu, port))),
<set> -> (if ((fmus(fmu).mode) = <EVENT>)
then calculateInput(I, mk_FMURef(fmu, port))
else setPort(I, mk_FMURef(fmu, port))),
<step> -> stepFMU(I, ((I.scenario).fmus)(fmu)),
<setC> -> setClock(I, ((I.scenario).fmus)(fmu), port, true),
<get> -> queryClock(I, ((I.scenario).fmus)(fmu), port)
others -> I
end)
	pre let fmus:map (Name) to (FMU) = ((I.scenario).fmus), mk_Action(actionType, fmu, port):Action = action in (cases actionType :
<get> -> (if ((fmus(fmu).mode) = <EVENT>)
then pre_calculateOutput(I, mk_FMURef(fmu, port))
else pre_getPort(I, mk_FMURef(fmu, port))),
<set> -> (if ((fmus(fmu).mode) = <EVENT>)
then pre_calculateInput(I, mk_FMURef(fmu, port))
else pre_setPort(I, mk_FMURef(fmu, port))),
<step> -> pre_stepFMU(I, ((I.scenario).fmus)(fmu)),
<setC> -> pre_setClock(I, ((I.scenario).fmus)(fmu), port, true),
<get> -> pre_queryClock(I, ((I.scenario).fmus)(fmu), port)
others -> false
end)\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1090:5\<close>

\<comment>\<open>VDM source: pre_runAction: (Importer * Action +> bool)
	pre_runAction(I, action) ==
let fmus:map (Name) to (FMU) = ((I.scenario).fmus), mk_Action(actionType, fmu, port):Action = action in (cases actionType :
<get> -> (if ((fmus(fmu).mode) = <EVENT>)
then pre_calculateOutput(I, mk_FMURef(fmu, port))
else pre_getPort(I, mk_FMURef(fmu, port))),
<set> -> (if ((fmus(fmu).mode) = <EVENT>)
then pre_calculateInput(I, mk_FMURef(fmu, port))
else pre_setPort(I, mk_FMURef(fmu, port))),
<step> -> pre_stepFMU(I, ((I.scenario).fmus)(fmu)),
<setC> -> pre_setClock(I, ((I.scenario).fmus)(fmu), port, true),
<get> -> pre_queryClock(I, ((I.scenario).fmus)(fmu), port)
others -> false
end)\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1103:9\<close>
definition
	pre_runAction :: "Importer \<Rightarrow> Action \<Rightarrow> bool"
where
	"pre_runAction I   action \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `pre_runAction` specification.\<close>
		(inv_Importer I  \<and>  inv_Action action)  \<and> 
		\<comment>\<open>User defined body of pre_runAction.\<close>
		(
		let 
(fmus::(Name \<rightharpoonup> FMU)) = (fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I))
		;
		
(dummy0::Action) = action;
(dummy0::Action) = action;
(dummy0::Action) = action
		in
			let actionType = (actionType\<^sub>A\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n dummy0); fmu = (fmu\<^sub>A\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n dummy0); port = (port\<^sub>A\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n dummy0) in (if ((inv_Map ((inv_VDMSeq1' (inv_VDMChar))) inv_FMU  fmus))
	 \<and> 
	(inv_Action dummy0) then
			(
		case actionType of 
		get \<Rightarrow> (
		if (((mode\<^sub>F\<^sub>M\<^sub>U (the((fmus fmu)))) = FMUMode.U_EVENT )) then
		((pre_calculateOutput I   \<lparr>name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f = fmu, ref\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f = port\<rparr>))
		else
		((pre_getPort I   \<lparr>name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f = fmu, ref\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f = port\<rparr>)))
			  | 
			 set \<Rightarrow> (
		if (((mode\<^sub>F\<^sub>M\<^sub>U (the((fmus fmu)))) = FMUMode.U_EVENT )) then
		((pre_calculateInput I   \<lparr>name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f = fmu, ref\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f = port\<rparr>))
		else
		((pre_setPort I   \<lparr>name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f = fmu, ref\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f = port\<rparr>)))
			  | 
			 step \<Rightarrow> (pre_stepFMU I   ((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) fmu))
			  | 
			 setC \<Rightarrow> (pre_setClock I   ((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) fmu)   port   (True::\<bool>))
			  | 
			 get \<Rightarrow> (pre_queryClock I   ((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) fmu)   port)
			  | 
			 _ \<Rightarrow> (False::\<bool>))
		 else
			undefined
		)
		)"


\<comment>\<open>VDM source: post_runAction: (Importer * Action * Importer +> bool)
	post_runAction(I, action, RESULT) ==
null\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1090:5\<close>
definition
	post_runAction :: "Importer \<Rightarrow> Action \<Rightarrow> Importer \<Rightarrow> bool"
where
	"post_runAction I   action   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_runAction` specification.\<close>
		(inv_Importer I  \<and>  inv_Action action  \<and>  inv_Importer RESULT)"

definition
	runAction :: "Importer \<Rightarrow> Action \<Rightarrow> Importer"
where
	"runAction I   action \<equiv> 
	\<comment>\<open>User defined body of runAction.\<close>
	(
		let 
(fmus::(Name \<rightharpoonup> FMU)) = (fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I))
		;
		
(dummy0::Action) = action;
(dummy0::Action) = action;
(dummy0::Action) = action
		in
			let actionType = (actionType\<^sub>A\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n dummy0); fmu = (fmu\<^sub>A\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n dummy0); port = (port\<^sub>A\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n dummy0) in (if ((inv_Map ((inv_VDMSeq1' (inv_VDMChar))) inv_FMU  fmus))
	 \<and> 
	(inv_Action dummy0) then
			(
		case actionType of 
		get \<Rightarrow> (
		if (((mode\<^sub>F\<^sub>M\<^sub>U (the((fmus fmu)))) = FMUMode.U_EVENT )) then
		((calculateOutput I   \<lparr>name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f = fmu, ref\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f = port\<rparr>))
		else
		((getPort I   \<lparr>name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f = fmu, ref\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f = port\<rparr>)))
			  | 
			 set \<Rightarrow> (
		if (((mode\<^sub>F\<^sub>M\<^sub>U (the((fmus fmu)))) = FMUMode.U_EVENT )) then
		((calculateInput I   \<lparr>name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f = fmu, ref\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f = port\<rparr>))
		else
		((setPort I   \<lparr>name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f = fmu, ref\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f = port\<rparr>)))
			  | 
			 step \<Rightarrow> (stepFMU I   ((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) fmu))
			  | 
			 setC \<Rightarrow> (setClock I   ((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) fmu)   port   (True::\<bool>))
			  | 
			 get \<Rightarrow> (queryClock I   ((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) fmu)   port)
			  | 
			 _ \<Rightarrow> I)
		 else
			undefined
		)
		)"

	
	
\<comment>\<open>VDM source: isActionEnabled: (Importer * Action -> bool)
	isActionEnabled(I, action) ==
let mk_Action(actionType, fmu, port):Action = action in (cases actionType :
<get> -> (pre_preGetI(I, ((I.scenario).fmus)(fmu), port) and preGetI(I, ((I.scenario).fmus)(fmu), port)),
<set> -> (pre_preSetI(I, ((I.scenario).fmus)(fmu), port) and preSetI(I, ((I.scenario).fmus)(fmu), port)),
<step> -> (pre_preStepI(I, ((I.scenario).fmus)(fmu)) and preStepI(I, ((I.scenario).fmus)(fmu))),
<setC> -> (pre_preSetCI(I, ((I.scenario).fmus)(fmu), port) and preSetCI(I, ((I.scenario).fmus)(fmu), port)),
<getC> -> (pre_preGetCI(I, ((I.scenario).fmus)(fmu), port) and preGetCI(I, ((I.scenario).fmus)(fmu), port))
others -> false
end)
	pre true\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1118:5\<close>

\<comment>\<open>VDM source: pre_isActionEnabled: (Importer * Action +> bool)
	pre_isActionEnabled(I, action) ==
true\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1129:9\<close>
definition
	pre_isActionEnabled :: "Importer \<Rightarrow> Action \<Rightarrow> bool"
where
	"pre_isActionEnabled I   action \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `pre_isActionEnabled` specification.\<close>
		(inv_Importer I  \<and>  inv_Action action)  \<and> 
		\<comment>\<open>User defined body of pre_isActionEnabled.\<close>
		(True::\<bool>)"


\<comment>\<open>VDM source: post_isActionEnabled: (Importer * Action * bool +> bool)
	post_isActionEnabled(I, action, RESULT) ==
null\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1118:5\<close>
definition
	post_isActionEnabled :: "Importer \<Rightarrow> Action \<Rightarrow> bool \<Rightarrow> bool"
where
	"post_isActionEnabled I   action   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_isActionEnabled` specification.\<close>
		(inv_Importer I  \<and>  inv_Action action  \<and>  (inv_bool RESULT))"

definition
	isActionEnabled :: "Importer \<Rightarrow> Action \<Rightarrow> bool"
where
	"isActionEnabled I   action \<equiv> 
	\<comment>\<open>User defined body of isActionEnabled.\<close>
	(
		let 
(dummy0::Action) = action;
(dummy0::Action) = action;
(dummy0::Action) = action
		in
			let actionType = (actionType\<^sub>A\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n dummy0); fmu = (fmu\<^sub>A\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n dummy0); port = (port\<^sub>A\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n dummy0) in (if (inv_Action dummy0) then
			(
		case actionType of 
		get \<Rightarrow> ((pre_preGetI I   ((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) fmu)   port) \<and> (preGetI I   ((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) fmu)   port))
			  | 
			 set \<Rightarrow> ((pre_preSetI I   ((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) fmu)   port) \<and> (preSetI I   ((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) fmu)   port))
			  | 
			 step \<Rightarrow> ((pre_preStepI I   ((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) fmu)) \<and> (preStepI I   ((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) fmu)))
			  | 
			 setC \<Rightarrow> ((pre_preSetCI I   ((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) fmu)   port) \<and> (preSetCI I   ((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) fmu)   port))
			  | 
			 getC \<Rightarrow> ((pre_preGetCI I   ((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) fmu)   port) \<and> (preGetCI I   ((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) fmu)   port))
			  | 
			 _ \<Rightarrow> (False::\<bool>))
		 else
			undefined
		)
		)"

	
	
\<comment>\<open>VDM source: runAlgorithm: (Importer * seq of (Action) -> Importer)
	runAlgorithm(I, algorithm) ==
(if (algorithm = [])
then I
else let action in set {action | action in seq algorithm & (pre_isActionEnabled(I, action) and isActionEnabled(I, action))} in runAlgorithm(runAction(I, action), [act | act in set ((elems algorithm) \ {action})]))
	pre ((algorithm <> []) => let action in set {action | action in set (elems algorithm) & (pre_isActionEnabled(I, action) and isActionEnabled(I, action))} in (pre_runAction(I, action) and pre_runAlgorithm(runAction(I, action), [act | act in set ((elems algorithm) \ {action})])))
	measure (len algorithm)\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1136:5\<close>

\<comment>\<open>VDM source: pre_runAlgorithm: (Importer * seq of (Action) +> bool)
	pre_runAlgorithm(I, algorithm) ==
((algorithm <> []) => let action in set {action | action in set (elems algorithm) & (pre_isActionEnabled(I, action) and isActionEnabled(I, action))} in (pre_runAction(I, action) and pre_runAlgorithm(runAction(I, action), [act | act in set ((elems algorithm) \ {action})])))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1148:25\<close>
definition
	pre_runAlgorithm :: "Importer \<Rightarrow> Action VDMSeq \<Rightarrow> bool"
where
	"pre_runAlgorithm I   algorithm \<equiv> 
	\<comment>\<open>Implicitly defined type invariant checks for  `pre_runAlgorithm` specification.\<close>
	(inv_Importer I  \<and>  (inv_VDMSeq' inv_Action  algorithm))  \<and> 
	\<comment>\<open>User defined body of pre_runAlgorithm.\<close>
	((algorithm \<noteq> []) \<longrightarrow> (
		SOME (dummy0::bool) .(dummy0 \<in> { ((pre_runAction I   action) \<and> (pre_runAlgorithm (runAction I   action)   [ act . act \<leftarrow> sorted_list_of_set (((elems algorithm) - {action})) , ((act \<in>((elems algorithm) - {action}))) ]
	\<comment>\<open>`Set bind `(act \<in> ((elems algorithm) - {action}))` in sequence comprehension requires its Isabelle type to instantiate class linorder.`   This can be a problem if the target type of @{term \<open>((elems algorithm) - {action})\<close>}   has a VDM ord_ predicate.\<close> )) | action .  ((action \<in>{ action .   ((action \<in>(elems algorithm)))  \<and> ((pre_isActionEnabled I   action) \<and> (isActionEnabled I   action)) }))  })))"


\<comment>\<open>VDM source: post_runAlgorithm: (Importer * seq of (Action) * Importer +> bool)
	post_runAlgorithm(I, algorithm, RESULT) ==
null\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1136:5\<close>
definition
	post_runAlgorithm :: "Importer \<Rightarrow> Action VDMSeq \<Rightarrow> Importer \<Rightarrow> bool"
where
	"post_runAlgorithm I   algorithm   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_runAlgorithm` specification.\<close>
		(inv_Importer I  \<and>  (inv_VDMSeq' inv_Action  algorithm)  \<and>  inv_Importer RESULT)"

fun
	runAlgorithm :: "Importer \<Rightarrow> Action VDMSeq \<Rightarrow> Importer"
where
	"runAlgorithm I   algorithm = 
	\<comment>\<open>User defined body of runAlgorithm.\<close>
	(
		if ((algorithm = [])) then
		(I)
		else
		((
		SOME (dummy0::Importer) .(dummy0 \<in> { (runAlgorithm (runAction I   action)   [ act . act \<leftarrow> sorted_list_of_set (((elems algorithm) - {action})) , ((act \<in>((elems algorithm) - {action}))) ]
	\<comment>\<open>`Set bind `(act \<in> ((elems algorithm) - {action}))` in sequence comprehension requires its Isabelle type to instantiate class linorder.`   This can be a problem if the target type of @{term \<open>((elems algorithm) - {action})\<close>}   has a VDM ord_ predicate.\<close> ) | action .  ((action \<in>{ action .   ((action \<in>(elems algorithm)))  \<and> ((pre_isActionEnabled I   action) \<and> (isActionEnabled I   action)) }))  }))))"

	
	
\<comment>\<open>VDM source: exchangeActions: (map (FMURef) to (FMURef) -> seq of (Action))
	exchangeActions(connections) ==
let outputs:set of (Action) = {mk_Action(<get>, (outputVar.name), (outputVar.ref)) | outputVar in set (dom connections)}, inputs:set of (Action) = {mk_Action(<set>, (inputVar.name), (inputVar.ref)) | inputVar in set (rng connections)}, portsActions:set of (Action) = (outputs union inputs) in [act | act in set portsActions]
	pre true
	post ((len RESULT) = ((card (dom connections)) + (card (rng connections))))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1158:5\<close>

\<comment>\<open>VDM source: pre_exchangeActions: (map (FMURef) to (FMURef) +> bool)
	pre_exchangeActions(connections) ==
true\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1164:9\<close>
definition
	pre_exchangeActions :: "(FMURef \<rightharpoonup> FMURef) \<Rightarrow> bool"
where
	"pre_exchangeActions connections \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `pre_exchangeActions` specification.\<close>
		((inv_Map inv_FMURef  inv_FMURef  connections))  \<and> 
		\<comment>\<open>User defined body of pre_exchangeActions.\<close>
		(True::\<bool>)"


\<comment>\<open>VDM source: post_exchangeActions: (map (FMURef) to (FMURef) * seq of (Action) +> bool)
	post_exchangeActions(connections, RESULT) ==
((len RESULT) = ((card (dom connections)) + (card (rng connections))))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1165:22\<close>
definition
	post_exchangeActions :: "(FMURef \<rightharpoonup> FMURef) \<Rightarrow> Action VDMSeq \<Rightarrow> bool"
where
	"post_exchangeActions connections   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `post_exchangeActions` specification.\<close>
		((inv_Map inv_FMURef  inv_FMURef  connections)  \<and>  (inv_VDMSeq' inv_Action  RESULT))  \<and> 
		\<comment>\<open>User defined body of post_exchangeActions.\<close>
		((len RESULT) = ((vdm_card (dom connections)) + (vdm_card (rng connections))))"

definition
	exchangeActions :: "(FMURef \<rightharpoonup> FMURef) \<Rightarrow> Action VDMSeq"
where
	"exchangeActions connections \<equiv> 
	\<comment>\<open>User defined body of exchangeActions.\<close>
	(
		let 
(outputs::Action VDMSet) = { \<lparr>actionType\<^sub>A\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n = U_get ActionType.U_get , fmu\<^sub>A\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n = (name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f outputVar), port\<^sub>A\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n = (ref\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f outputVar)\<rparr> | outputVar .  ((outputVar \<in>(dom connections)))  }
		;
		
(inputs::Action VDMSet) = { \<lparr>actionType\<^sub>A\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n = U_set ActionType.U_set , fmu\<^sub>A\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n = (name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f inputVar), port\<^sub>A\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n = (ref\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f inputVar)\<rparr> | inputVar .  ((inputVar \<in>(rng connections)))  }
		;
		
(portsActions::Action VDMSet) = (outputs \<union> inputs)
		in
			(if ((inv_VDMSet' inv_Action  outputs))
	 \<and> 
	((inv_VDMSet' inv_Action  inputs))
	 \<and> 
	((inv_VDMSet' inv_Action  portsActions)) then
			[
		act
		.
		act \<leftarrow> sorted_list_of_set (portsActions)
		,
		((act \<in>portsActions))
		]
	\<comment>\<open>`Set bind `(act \<in> portsActions)` in sequence comprehension requires its Isabelle type to instantiate class linorder.` 
		 This can be a problem if the target type of @{term \<open>portsActions\<close>} 
		 has a VDM ord_ predicate.\<close>
		
		 else
			undefined
		)
		)"

	
	
\<comment>\<open>VDM source: initializeData: (Importer -> Importer)
	initializeData(I) ==
let actions:seq of (Action) = exchangeActions((((I.scenario).connections).dataConnections)) in runAlgorithm(I, actions)
	pre (pre_preInitialization(I) and (preInitialization(I) and (pre_exchangeActions((((I.scenario).connections).dataConnections)) and pre_runAlgorithm(I, exchangeActions((((I.scenario).connections).dataConnections))))))
	post (pre_postInitialization(RESULT) and postInitialization(RESULT))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1172:5\<close>

\<comment>\<open>VDM source: pre_initializeData: (Importer +> bool)
	pre_initializeData(I) ==
(pre_preInitialization(I) and (preInitialization(I) and (pre_exchangeActions((((I.scenario).connections).dataConnections)) and pre_runAlgorithm(I, exchangeActions((((I.scenario).connections).dataConnections))))))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1178:9\<close>
definition
	pre_initializeData :: "Importer \<Rightarrow> bool"
where
	"pre_initializeData I \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `pre_initializeData` specification.\<close>
		(inv_Importer I)  \<and> 
		\<comment>\<open>User defined body of pre_initializeData.\<close>
		((pre_preInitialization I) \<and> ((preInitialization I) \<and> ((pre_exchangeActions (dataConnections\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o\<^sub>C\<^sub>o\<^sub>n\<^sub>n\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n\<^sub>s (connections\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)))) \<and> (pre_runAlgorithm I   (exchangeActions (dataConnections\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o\<^sub>C\<^sub>o\<^sub>n\<^sub>n\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n\<^sub>s (connections\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I))))))))"


\<comment>\<open>VDM source: post_initializeData: (Importer * Importer +> bool)
	post_initializeData(I, RESULT) ==
(pre_postInitialization(RESULT) and postInitialization(RESULT))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1183:9\<close>
definition
	post_initializeData :: "Importer \<Rightarrow> Importer \<Rightarrow> bool"
where
	"post_initializeData I   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `post_initializeData` specification.\<close>
		(inv_Importer I  \<and>  inv_Importer RESULT)  \<and> 
		\<comment>\<open>User defined body of post_initializeData.\<close>
		((pre_postInitialization RESULT) \<and> (postInitialization RESULT))"

definition
	initializeData :: "Importer \<Rightarrow> Importer"
where
	"initializeData I \<equiv> 
	\<comment>\<open>User defined body of initializeData.\<close>
	(
		let 
(actions::Action VDMSeq) = (exchangeActions (dataConnections\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o\<^sub>C\<^sub>o\<^sub>n\<^sub>n\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n\<^sub>s (connections\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I))))
		in
			(if ((inv_VDMSeq' inv_Action  actions)) then
			(runAlgorithm I   actions)
		 else
			undefined
		)
		)"

	
	
\<comment>\<open>VDM source: tickingClocks: (Importer -> (Importer * set of (FMURef)))
	tickingClocks(I) ==
let clocksTickingNow:set of (Name) = (dom ((I.schedule) :> {((I.time).r)})), inputsToTick:set1 of (FMURef) = (dunion (rng (clocksTickingNow <: (((I.scenario).connections).timedClockConnections)))), relevantTimeBasedClocks:set of (TimeBasedClock) = {clock | clock in set ((I.scenario).timeBasedClocks) & ((clock.name) in set clocksTickingNow)}, updatedSchedule:map (Name) to (Real1) = {(c.name) |-> ((c.period) + ((I.time).r)) | c in set relevantTimeBasedClocks}, I1:Importer = mu(I, relevantInputClocks |-> inputsToTick, schedule |-> ((I.schedule) ++ updatedSchedule)) in mk_(I1, inputsToTick)
	pre true
	post ((((dom ((I.schedule) :> {((I.time).r)})) = {}) <=> ((RESULT.#1) = I)) and (((dom ((I.schedule) :> {((I.time).r)})) <> {}) <=> ((RESULT.#2) <> {})))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1188:5\<close>

\<comment>\<open>VDM source: pre_tickingClocks: (Importer +> bool)
	pre_tickingClocks(I) ==
true\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1203:9\<close>
definition
	pre_tickingClocks :: "Importer \<Rightarrow> bool"
where
	"pre_tickingClocks I \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `pre_tickingClocks` specification.\<close>
		(inv_Importer I)  \<and> 
		\<comment>\<open>User defined body of pre_tickingClocks.\<close>
		(True::\<bool>)"


\<comment>\<open>VDM source: post_tickingClocks: (Importer * (Importer * set of (FMURef)) +> bool)
	post_tickingClocks(I, RESULT) ==
((((dom ((I.schedule) :> {((I.time).r)})) = {}) <=> ((RESULT.#1) = I)) and (((dom ((I.schedule) :> {((I.time).r)})) <> {}) <=> ((RESULT.#2) <> {})))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1206:9\<close>
definition
	post_tickingClocks :: "Importer \<Rightarrow> (Importer \<times> FMURef VDMSet) \<Rightarrow> bool"
where
	"post_tickingClocks I   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `post_tickingClocks` specification.\<close>
		(inv_Importer I  \<and>  
		(inv_Importer (fst RESULT)\<and>
		 (inv_VDMSet' inv_FMURef  (snd RESULT))
		))  \<and> 
		\<comment>\<open>User defined body of post_tickingClocks.\<close>
		((((dom ((schedule\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I) \<triangleright> {(r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I))})) = {}) \<longleftrightarrow> ((fst (RESULT)) = I)) \<and> (((dom ((schedule\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I) \<triangleright> {(r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I))})) \<noteq> {}) \<longleftrightarrow> ((snd (RESULT)) \<noteq> {})))"

definition
	tickingClocks :: "Importer \<Rightarrow> (Importer \<times> FMURef VDMSet)"
where
	"tickingClocks I \<equiv> 
	\<comment>\<open>User defined body of tickingClocks.\<close>
	(
		let 
(clocksTickingNow::Name VDMSet) = (dom ((schedule\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I) \<triangleright> {(r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I))}))
		;
		
(inputsToTick::FMURef VDMSet1) = (\<Union> (rng (clocksTickingNow \<triangleleft> (timedClockConnections\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o\<^sub>C\<^sub>o\<^sub>n\<^sub>n\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n\<^sub>s (connections\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I))))))
		;
		
(relevantTimeBasedClocks::TimeBasedClock VDMSet) = { clock .   ((clock \<in>(timeBasedClocks\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I))))  \<and> ((name\<^sub>T\<^sub>i\<^sub>m\<^sub>e\<^sub>B\<^sub>a\<^sub>s\<^sub>e\<^sub>d\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k clock) \<in> clocksTickingNow) }
		;
		
(updatedSchedule::(Name \<rightharpoonup> Real1)) = (\<comment>\<open>VDM Map comprehension is translated as a lambda-term through mapCompSetBound\<close>
		mapCompSetBound 
		{(name\<^sub>T\<^sub>i\<^sub>m\<^sub>e\<^sub>B\<^sub>a\<^sub>s\<^sub>e\<^sub>d\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k c)} 
		{((period\<^sub>T\<^sub>i\<^sub>m\<^sub>e\<^sub>B\<^sub>a\<^sub>s\<^sub>e\<^sub>d\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k c) + (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)))} 
		((inv_VDMSeq1' (inv_VDMChar))) 
		(inv_VDMReal) 
		(
	\<lambda> (dummy0DOMAIN :: Name)   (dummy0RANGE :: VDMReal) .
		(if ((((inv_VDMSeq1' (inv_VDMChar) dummy0DOMAIN))))  \<and>  (((inv_VDMReal dummy0RANGE))) \<and> ((inv_VDMSeq1' (inv_VDMChar) (
		if ((\<exists> (dummy0DOMAIN :: Name)  . (((((inv_VDMSeq1' (inv_VDMChar) dummy0DOMAIN)))) \<longrightarrow> ((dummy0DOMAIN = (name\<^sub>T\<^sub>i\<^sub>m\<^sub>e\<^sub>B\<^sub>a\<^sub>s\<^sub>e\<^sub>d\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k c)) \<and> (True::\<bool>))))) then
		(dummy0DOMAIN)
		else
		(undefined)))) then
			(
		if ((\<exists> (dummy0DOMAIN :: Name)  . (((((inv_VDMSeq1' (inv_VDMChar) dummy0DOMAIN)))) \<longrightarrow> ((dummy0DOMAIN = (name\<^sub>T\<^sub>i\<^sub>m\<^sub>e\<^sub>B\<^sub>a\<^sub>s\<^sub>e\<^sub>d\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k c)) \<and> (True::\<bool>))))) then
		(dummy0DOMAIN)
		else
		(undefined))
		 else
			undefined
		)
		) 
		(
	\<lambda> (dummy0DOMAIN :: Name)   (dummy0RANGE :: VDMReal) .
		(if ((((inv_VDMSeq1' (inv_VDMChar) dummy0DOMAIN))))  \<and>  (((inv_VDMReal dummy0RANGE))) \<and> (inv_VDMReal (
		if ((\<exists> (dummy0RANGE :: VDMReal)  . ((((inv_VDMReal dummy0RANGE))) \<longrightarrow> ((dummy0RANGE = ((period\<^sub>T\<^sub>i\<^sub>m\<^sub>e\<^sub>B\<^sub>a\<^sub>s\<^sub>e\<^sub>d\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k c) + (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)))) \<and> (True::\<bool>))))) then
		(dummy0RANGE)
		else
		(undefined))) then
			(
		if ((\<exists> (dummy0RANGE :: VDMReal)  . ((((inv_VDMReal dummy0RANGE))) \<longrightarrow> ((dummy0RANGE = ((period\<^sub>T\<^sub>i\<^sub>m\<^sub>e\<^sub>B\<^sub>a\<^sub>s\<^sub>e\<^sub>d\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k c) + (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)))) \<and> (True::\<bool>))))) then
		(dummy0RANGE)
		else
		(undefined))
		 else
			undefined
		)
		) 
		(truecnst ))
		;
		
(I1::Importer) = (I)\<lparr>relevantInputClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r := inputsToTick, schedule\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r := ((schedule\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I) \<dagger> updatedSchedule)\<rparr>
		in
			(if ((inv_VDMSet' ((inv_VDMSeq1' (inv_VDMChar))) clocksTickingNow))
	 \<and> 
	((inv_VDMSet1' inv_FMURef  inputsToTick))
	 \<and> 
	((inv_VDMSet' inv_TimeBasedClock  relevantTimeBasedClocks))
	 \<and> 
	((inv_Map ((inv_VDMSeq1' (inv_VDMChar))) ((inv_VDMReal)) updatedSchedule))
	 \<and> 
	(inv_Importer I1) then
			(I1 , inputsToTick)
		 else
			undefined
		)
		)"

	
	
\<comment>\<open>VDM source: fmusToAdd: (Scenario * set of (Name) * set of (Name) -> set of (Name))
	fmusToAdd(M, addedFMUs, notAddedFMUS) ==
{(((M.connections).clockConnections)(con).name) | con in set (dom ((M.connections).clockConnections)) & (((con.name) in set addedFMUs) and ((((M.connections).clockConnections)(con).name) in set notAddedFMUS))}
	pre ((addedFMUs inter notAddedFMUS) = {})
	post (RESULT subset notAddedFMUS)\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1209:5\<close>

\<comment>\<open>VDM source: pre_fmusToAdd: (Scenario * set of (Name) * set of (Name) +> bool)
	pre_fmusToAdd(M, addedFMUs, notAddedFMUS) ==
((addedFMUs inter notAddedFMUS) = {})\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1213:38\<close>
definition
	pre_fmusToAdd :: "Scenario \<Rightarrow> Name VDMSet \<Rightarrow> Name VDMSet \<Rightarrow> bool"
where
	"pre_fmusToAdd M   addedFMUs   notAddedFMUS \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `pre_fmusToAdd` specification.\<close>
		(inv_Scenario M  \<and>  (inv_VDMSet' (inv_Name) addedFMUs)  \<and>  (inv_VDMSet' (inv_Name) notAddedFMUS))  \<and> 
		\<comment>\<open>User defined body of pre_fmusToAdd.\<close>
		((addedFMUs \<inter> notAddedFMUS) = {})"


\<comment>\<open>VDM source: post_fmusToAdd: (Scenario * set of (Name) * set of (Name) * set of (Name) +> bool)
	post_fmusToAdd(M, addedFMUs, notAddedFMUS, RESULT) ==
(RESULT subset notAddedFMUS)\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1214:17\<close>
definition
	post_fmusToAdd :: "Scenario \<Rightarrow> Name VDMSet \<Rightarrow> Name VDMSet \<Rightarrow> Name VDMSet \<Rightarrow> bool"
where
	"post_fmusToAdd M   addedFMUs   notAddedFMUS   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `post_fmusToAdd` specification.\<close>
		(inv_Scenario M  \<and>  (inv_VDMSet' (inv_Name) addedFMUs)  \<and>  (inv_VDMSet' (inv_Name) notAddedFMUS)  \<and>  (inv_VDMSet' (inv_Name) RESULT))  \<and> 
		\<comment>\<open>User defined body of post_fmusToAdd.\<close>
		(RESULT \<subseteq> notAddedFMUS)"

definition
	fmusToAdd :: "Scenario \<Rightarrow> Name VDMSet \<Rightarrow> Name VDMSet \<Rightarrow> Name VDMSet"
where
	"fmusToAdd M   addedFMUs   notAddedFMUS \<equiv> 
	\<comment>\<open>User defined body of fmusToAdd.\<close>
	{ (name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f (the(((clockConnections\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o\<^sub>C\<^sub>o\<^sub>n\<^sub>n\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n\<^sub>s (connections\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o M)) con)))) | con .  ((con \<in>(dom (clockConnections\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o\<^sub>C\<^sub>o\<^sub>n\<^sub>n\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n\<^sub>s (connections\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o M)))))  \<and> (((name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f con) \<in> addedFMUs) \<and> ((name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f (the(((clockConnections\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o\<^sub>C\<^sub>o\<^sub>n\<^sub>n\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n\<^sub>s (connections\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o M)) con)))) \<in> notAddedFMUS)) }"

	
	
\<comment>\<open>VDM source: calculateRelevantFMUs: (Scenario * set of (Name) * set of (Name) -> set of (Name))
	calculateRelevantFMUs(M, relevantFMUs, notRelevantFMUs) ==
let addedFMUs:set of (Name) = fmusToAdd(M, relevantFMUs, notRelevantFMUs) in (if (addedFMUs = {})
then relevantFMUs
else calculateRelevantFMUs(M, (relevantFMUs union addedFMUs), (notRelevantFMUs \ addedFMUs)))
	pre (((relevantFMUs inter notRelevantFMUs) = {}) and (((relevantFMUs union notRelevantFMUs) = (dom (M.fmus))) and (pre_fmusToAdd(M, relevantFMUs, notRelevantFMUs) and let addedFMUs:set of (Name) = fmusToAdd(M, relevantFMUs, notRelevantFMUs) in ((addedFMUs <> {}) => pre_calculateRelevantFMUs(M, (relevantFMUs union addedFMUs), (notRelevantFMUs \ addedFMUs))))))
	post ((RESULT subset (dom (M.fmus))) and let notAdded:set of (Name) = ((dom (M.fmus)) \ RESULT) in (not (exists [srcClock in set (dom ((M.connections).clockConnections))] & (((srcClock.name) in set RESULT) and ((((M.connections).clockConnections)(srcClock).name) in set notAdded)))))
	measure (card notRelevantFMUs)\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1221:5\<close>

\<comment>\<open>VDM source: pre_calculateRelevantFMUs: (Scenario * set of (Name) * set of (Name) +> bool)
	pre_calculateRelevantFMUs(M, relevantFMUs, notRelevantFMUs) ==
(((relevantFMUs inter notRelevantFMUs) = {}) and (((relevantFMUs union notRelevantFMUs) = (dom (M.fmus))) and (pre_fmusToAdd(M, relevantFMUs, notRelevantFMUs) and let addedFMUs:set of (Name) = fmusToAdd(M, relevantFMUs, notRelevantFMUs) in ((addedFMUs <> {}) => pre_calculateRelevantFMUs(M, (relevantFMUs union addedFMUs), (notRelevantFMUs \ addedFMUs))))))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1230:13\<close>
definition
	pre_calculateRelevantFMUs :: "Scenario \<Rightarrow> Name VDMSet \<Rightarrow> Name VDMSet \<Rightarrow> bool"
where
	"pre_calculateRelevantFMUs M   relevantFMUs   notRelevantFMUs \<equiv> 
	\<comment>\<open>Implicitly defined type invariant checks for  `pre_calculateRelevantFMUs` specification.\<close>
	(inv_Scenario M  \<and>  (inv_VDMSet' (inv_Name) relevantFMUs)  \<and>  (inv_VDMSet' (inv_Name) notRelevantFMUs))  \<and> 
	\<comment>\<open>User defined body of pre_calculateRelevantFMUs.\<close>
	(((relevantFMUs \<inter> notRelevantFMUs) = {}) \<and> (((relevantFMUs \<union> notRelevantFMUs) = (dom (fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o M))) \<and> ((pre_fmusToAdd M   relevantFMUs   notRelevantFMUs) \<and> (
		let 
(addedFMUs::Name VDMSet) = (fmusToAdd M   relevantFMUs   notRelevantFMUs)
		in
			(if ((inv_VDMSet' ((inv_VDMSeq1' (inv_VDMChar))) addedFMUs)) then
			((addedFMUs \<noteq> {}) \<longrightarrow> (pre_calculateRelevantFMUs M   (relevantFMUs \<union> addedFMUs)   (notRelevantFMUs - addedFMUs)))
		 else
			undefined
		)
		))))"


\<comment>\<open>VDM source: post_calculateRelevantFMUs: (Scenario * set of (Name) * set of (Name) * set of (Name) +> bool)
	post_calculateRelevantFMUs(M, relevantFMUs, notRelevantFMUs, RESULT) ==
((RESULT subset (dom (M.fmus))) and let notAdded:set of (Name) = ((dom (M.fmus)) \ RESULT) in (not (exists [srcClock in set (dom ((M.connections).clockConnections))] & (((srcClock.name) in set RESULT) and ((((M.connections).clockConnections)(srcClock).name) in set notAdded)))))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1237:13\<close>
definition
	post_calculateRelevantFMUs :: "Scenario \<Rightarrow> Name VDMSet \<Rightarrow> Name VDMSet \<Rightarrow> Name VDMSet \<Rightarrow> bool"
where
	"post_calculateRelevantFMUs M   relevantFMUs   notRelevantFMUs   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `post_calculateRelevantFMUs` specification.\<close>
		(inv_Scenario M  \<and>  (inv_VDMSet' (inv_Name) relevantFMUs)  \<and>  (inv_VDMSet' (inv_Name) notRelevantFMUs)  \<and>  (inv_VDMSet' (inv_Name) RESULT))  \<and> 
		\<comment>\<open>User defined body of post_calculateRelevantFMUs.\<close>
		((RESULT \<subseteq> (dom (fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o M))) \<and> (
		let 
(notAdded::Name VDMSet) = ((dom (fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o M)) - RESULT)
		in
			(if ((inv_VDMSet' ((inv_VDMSeq1' (inv_VDMChar))) notAdded)) then
			(\<not> (\<exists> srcClock \<in> (dom (clockConnections\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o\<^sub>C\<^sub>o\<^sub>n\<^sub>n\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n\<^sub>s (connections\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o M)))  . (((name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f srcClock) \<in> RESULT) \<and> ((name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f (the(((clockConnections\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o\<^sub>C\<^sub>o\<^sub>n\<^sub>n\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n\<^sub>s (connections\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o M)) srcClock)))) \<in> notAdded))))
		 else
			undefined
		)
		))"

fun
	calculateRelevantFMUs :: "Scenario \<Rightarrow> Name VDMSet \<Rightarrow> Name VDMSet \<Rightarrow> Name VDMSet"
where
	"calculateRelevantFMUs M   relevantFMUs   notRelevantFMUs = 
	\<comment>\<open>User defined body of calculateRelevantFMUs.\<close>
	(
		let 
(addedFMUs::Name VDMSet) = (fmusToAdd M   relevantFMUs   notRelevantFMUs)
		in
			(if ((inv_VDMSet' ((inv_VDMSeq1' (inv_VDMChar))) addedFMUs)) then
			(
		if ((addedFMUs = {})) then
		(relevantFMUs)
		else
		((calculateRelevantFMUs M   (relevantFMUs \<union> addedFMUs)   (notRelevantFMUs - addedFMUs))))
		 else
			undefined
		)
		)"

	
	
\<comment>\<open>VDM source: preCoSimulationStep: (Scenario * Time -> bool)
	preCoSimulationStep(scenario, time) ==
let fmus:set1 of (FMU) = (rng (scenario.fmus)) in (pre_assertFMUMode(fmus, {<STEP>}) and (assertFMUMode(fmus, {<STEP>}) and (pre_variablesSynchronized(scenario, {<continous>}) and (variablesSynchronized(scenario, {<continous>}) and (pre_fmusSynchronizedAtTime(fmus, time) and fmusSynchronizedAtTime(fmus, time))))))
	pre true\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1247:5\<close>

\<comment>\<open>VDM source: pre_preCoSimulationStep: (Scenario * Time +> bool)
	pre_preCoSimulationStep(scenario, time) ==
true\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1256:9\<close>
definition
	pre_preCoSimulationStep :: "Scenario \<Rightarrow> Time \<Rightarrow> bool"
where
	"pre_preCoSimulationStep scenario   time \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `pre_preCoSimulationStep` specification.\<close>
		(inv_Scenario scenario  \<and>  inv_Time time)  \<and> 
		\<comment>\<open>User defined body of pre_preCoSimulationStep.\<close>
		(True::\<bool>)"


\<comment>\<open>VDM source: post_preCoSimulationStep: (Scenario * Time * bool +> bool)
	post_preCoSimulationStep(scenario, time, RESULT) ==
null\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1247:5\<close>
definition
	post_preCoSimulationStep :: "Scenario \<Rightarrow> Time \<Rightarrow> bool \<Rightarrow> bool"
where
	"post_preCoSimulationStep scenario   time   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_preCoSimulationStep` specification.\<close>
		(inv_Scenario scenario  \<and>  inv_Time time  \<and>  (inv_bool RESULT))"

definition
	preCoSimulationStep :: "Scenario \<Rightarrow> Time \<Rightarrow> bool"
where
	"preCoSimulationStep scenario   time \<equiv> 
	\<comment>\<open>User defined body of preCoSimulationStep.\<close>
	(
		let 
(fmus::FMU VDMSet1) = (rng (fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o scenario))
		in
			(if ((inv_VDMSet1' inv_FMU  fmus)) then
			((pre_assertFMUMode fmus   {FMUMode.U_STEP }) \<and> ((assertFMUMode fmus   {FMUMode.U_STEP }) \<and> ((pre_variablesSynchronized scenario   {PortType.U_continous }) \<and> ((variablesSynchronized scenario   {PortType.U_continous }) \<and> ((pre_fmusSynchronizedAtTime fmus   time) \<and> (fmusSynchronizedAtTime fmus   time))))))
		 else
			undefined
		)
		)"

	
	
\<comment>\<open>VDM source: enterEventMode: (Importer * set1 of (Name) -> Importer)
	enterEventMode(I, fmus) ==
mu(I, scenario |-> mu((I.scenario), fmus |-> (((I.scenario).fmus) ++ {name |-> mu(((I.scenario).fmus)(name), mode |-> <EVENT>) | name in set ((dom ((I.scenario).fmus)) inter fmus)})))
	pre (pre_preCoSimulationStep((I.scenario), (I.time)) and preCoSimulationStep((I.scenario), (I.time)))
	post (pre_ImporterNotAffected(I, RESULT) and (ImporterNotAffected(I, RESULT) and (pre_variablesSynchronized((RESULT.scenario), {<continous>}) and (variablesSynchronized((RESULT.scenario), {<continous>}) and let fmusAffected:set of (FMU) = (rng (fmus <: ((RESULT.scenario).fmus))) in (pre_assertFMUMode(fmusAffected, {<EVENT>}) and (assertFMUMode(fmusAffected, {<EVENT>}) and (forall m' in set fmusAffected & (((m'.time).i) = 0))))))))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1262:5\<close>

\<comment>\<open>VDM source: pre_enterEventMode: (Importer * set1 of (Name) +> bool)
	pre_enterEventMode(I, fmus) ==
(pre_preCoSimulationStep((I.scenario), (I.time)) and preCoSimulationStep((I.scenario), (I.time)))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1269:9\<close>
definition
	pre_enterEventMode :: "Importer \<Rightarrow> Name VDMSet1 \<Rightarrow> bool"
where
	"pre_enterEventMode I   fmus \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `pre_enterEventMode` specification.\<close>
		(inv_Importer I  \<and>  (inv_VDMSet1' (inv_Name) fmus))  \<and> 
		\<comment>\<open>User defined body of pre_enterEventMode.\<close>
		((pre_preCoSimulationStep (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)   (time\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) \<and> (preCoSimulationStep (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)   (time\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)))"


\<comment>\<open>VDM source: post_enterEventMode: (Importer * set1 of (Name) * Importer +> bool)
	post_enterEventMode(I, fmus, RESULT) ==
(pre_ImporterNotAffected(I, RESULT) and (ImporterNotAffected(I, RESULT) and (pre_variablesSynchronized((RESULT.scenario), {<continous>}) and (variablesSynchronized((RESULT.scenario), {<continous>}) and let fmusAffected:set of (FMU) = (rng (fmus <: ((RESULT.scenario).fmus))) in (pre_assertFMUMode(fmusAffected, {<EVENT>}) and (assertFMUMode(fmusAffected, {<EVENT>}) and (forall m' in set fmusAffected & (((m'.time).i) = 0))))))))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1272:9\<close>
definition
	post_enterEventMode :: "Importer \<Rightarrow> Name VDMSet1 \<Rightarrow> Importer \<Rightarrow> bool"
where
	"post_enterEventMode I   fmus   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `post_enterEventMode` specification.\<close>
		(inv_Importer I  \<and>  (inv_VDMSet1' (inv_Name) fmus)  \<and>  inv_Importer RESULT)  \<and> 
		\<comment>\<open>User defined body of post_enterEventMode.\<close>
		((pre_ImporterNotAffected I   RESULT) \<and> ((ImporterNotAffected I   RESULT) \<and> ((pre_variablesSynchronized (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r RESULT)   {PortType.U_continous }) \<and> ((variablesSynchronized (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r RESULT)   {PortType.U_continous }) \<and> (
		let 
(fmusAffected::FMU VDMSet) = (rng (fmus \<triangleleft> (fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r RESULT))))
		in
			(if ((inv_VDMSet' inv_FMU  fmusAffected)) then
			((pre_assertFMUMode fmusAffected   {FMUMode.U_EVENT }) \<and> ((assertFMUMode fmusAffected   {FMUMode.U_EVENT }) \<and> (\<forall> m' \<in> fmusAffected  . ((i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U m')) = (0::VDMNat)))))
		 else
			undefined
		)
		)))))"

definition
	enterEventMode :: "Importer \<Rightarrow> Name VDMSet1 \<Rightarrow> Importer"
where
	"enterEventMode I   fmus \<equiv> 
	\<comment>\<open>User defined body of enterEventMode.\<close>
	(I)\<lparr>scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r := ((scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I))\<lparr>fmus\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r := ((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) \<dagger> (\<comment>\<open>VDM Map comprehension is translated as a lambda-term through mapCompSetBound\<close>
		mapCompSetBound 
		{ name .   ((name \<in>((dom (fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I))) \<inter> fmus)))  } 
		{(((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) name))\<lparr>mode\<^sub>F\<^sub>M\<^sub>U := FMUMode.U_EVENT \<rparr>} 
		(inv_VDMSeq1' (inv_VDMChar)) 
		 (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U FMU))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U FMU)))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U FMU))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U FMU)))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U FMU))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U FMU))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U FMU))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U FMU)))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U FMU))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U FMU)))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U FMU)))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U FMU))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U FMU))) ) 
		(domid ) 
		(
	\<lambda> (dummy0DOMAIN :: VDMChar VDMSeq1)   (dummy0RANGE :: FMU) .
		(if (((inv_VDMSeq1' (inv_VDMChar) dummy0DOMAIN)))  \<and>  (( (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) ))) \<and>  (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U (
		if ((\<exists> (dummy0RANGE :: FMU)  . ((( (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) ))) \<longrightarrow> (\<comment>\<open>Transform a VDM `=` expression into an `eq_FMU` call\<close>
	(eq_FMU dummy0RANGE   (((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) name))\<lparr>mode\<^sub>F\<^sub>M\<^sub>U := FMUMode.U_EVENT \<rparr>) \<and> (True::\<bool>))))) then
		(dummy0RANGE)
		else
		(undefined))))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U (
		if ((\<exists> (dummy0RANGE :: FMU)  . ((( (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) ))) \<longrightarrow> (\<comment>\<open>Transform a VDM `=` expression into an `eq_FMU` call\<close>
	(eq_FMU dummy0RANGE   (((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) name))\<lparr>mode\<^sub>F\<^sub>M\<^sub>U := FMUMode.U_EVENT \<rparr>) \<and> (True::\<bool>))))) then
		(dummy0RANGE)
		else
		(undefined)))))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U (
		if ((\<exists> (dummy0RANGE :: FMU)  . ((( (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) ))) \<longrightarrow> (\<comment>\<open>Transform a VDM `=` expression into an `eq_FMU` call\<close>
	(eq_FMU dummy0RANGE   (((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) name))\<lparr>mode\<^sub>F\<^sub>M\<^sub>U := FMUMode.U_EVENT \<rparr>) \<and> (True::\<bool>))))) then
		(dummy0RANGE)
		else
		(undefined))))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U (
		if ((\<exists> (dummy0RANGE :: FMU)  . ((( (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) ))) \<longrightarrow> (\<comment>\<open>Transform a VDM `=` expression into an `eq_FMU` call\<close>
	(eq_FMU dummy0RANGE   (((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) name))\<lparr>mode\<^sub>F\<^sub>M\<^sub>U := FMUMode.U_EVENT \<rparr>) \<and> (True::\<bool>))))) then
		(dummy0RANGE)
		else
		(undefined)))))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U (
		if ((\<exists> (dummy0RANGE :: FMU)  . ((( (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) ))) \<longrightarrow> (\<comment>\<open>Transform a VDM `=` expression into an `eq_FMU` call\<close>
	(eq_FMU dummy0RANGE   (((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) name))\<lparr>mode\<^sub>F\<^sub>M\<^sub>U := FMUMode.U_EVENT \<rparr>) \<and> (True::\<bool>))))) then
		(dummy0RANGE)
		else
		(undefined))))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U (
		if ((\<exists> (dummy0RANGE :: FMU)  . ((( (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) ))) \<longrightarrow> (\<comment>\<open>Transform a VDM `=` expression into an `eq_FMU` call\<close>
	(eq_FMU dummy0RANGE   (((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) name))\<lparr>mode\<^sub>F\<^sub>M\<^sub>U := FMUMode.U_EVENT \<rparr>) \<and> (True::\<bool>))))) then
		(dummy0RANGE)
		else
		(undefined))))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U (
		if ((\<exists> (dummy0RANGE :: FMU)  . ((( (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) ))) \<longrightarrow> (\<comment>\<open>Transform a VDM `=` expression into an `eq_FMU` call\<close>
	(eq_FMU dummy0RANGE   (((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) name))\<lparr>mode\<^sub>F\<^sub>M\<^sub>U := FMUMode.U_EVENT \<rparr>) \<and> (True::\<bool>))))) then
		(dummy0RANGE)
		else
		(undefined))))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U (
		if ((\<exists> (dummy0RANGE :: FMU)  . ((( (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) ))) \<longrightarrow> (\<comment>\<open>Transform a VDM `=` expression into an `eq_FMU` call\<close>
	(eq_FMU dummy0RANGE   (((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) name))\<lparr>mode\<^sub>F\<^sub>M\<^sub>U := FMUMode.U_EVENT \<rparr>) \<and> (True::\<bool>))))) then
		(dummy0RANGE)
		else
		(undefined)))))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U (
		if ((\<exists> (dummy0RANGE :: FMU)  . ((( (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) ))) \<longrightarrow> (\<comment>\<open>Transform a VDM `=` expression into an `eq_FMU` call\<close>
	(eq_FMU dummy0RANGE   (((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) name))\<lparr>mode\<^sub>F\<^sub>M\<^sub>U := FMUMode.U_EVENT \<rparr>) \<and> (True::\<bool>))))) then
		(dummy0RANGE)
		else
		(undefined))))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U (
		if ((\<exists> (dummy0RANGE :: FMU)  . ((( (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) ))) \<longrightarrow> (\<comment>\<open>Transform a VDM `=` expression into an `eq_FMU` call\<close>
	(eq_FMU dummy0RANGE   (((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) name))\<lparr>mode\<^sub>F\<^sub>M\<^sub>U := FMUMode.U_EVENT \<rparr>) \<and> (True::\<bool>))))) then
		(dummy0RANGE)
		else
		(undefined)))))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U (
		if ((\<exists> (dummy0RANGE :: FMU)  . ((( (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) ))) \<longrightarrow> (\<comment>\<open>Transform a VDM `=` expression into an `eq_FMU` call\<close>
	(eq_FMU dummy0RANGE   (((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) name))\<lparr>mode\<^sub>F\<^sub>M\<^sub>U := FMUMode.U_EVENT \<rparr>) \<and> (True::\<bool>))))) then
		(dummy0RANGE)
		else
		(undefined)))))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U (
		if ((\<exists> (dummy0RANGE :: FMU)  . ((( (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) ))) \<longrightarrow> (\<comment>\<open>Transform a VDM `=` expression into an `eq_FMU` call\<close>
	(eq_FMU dummy0RANGE   (((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) name))\<lparr>mode\<^sub>F\<^sub>M\<^sub>U := FMUMode.U_EVENT \<rparr>) \<and> (True::\<bool>))))) then
		(dummy0RANGE)
		else
		(undefined))))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U (
		if ((\<exists> (dummy0RANGE :: FMU)  . ((( (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) ))) \<longrightarrow> (\<comment>\<open>Transform a VDM `=` expression into an `eq_FMU` call\<close>
	(eq_FMU dummy0RANGE   (((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) name))\<lparr>mode\<^sub>F\<^sub>M\<^sub>U := FMUMode.U_EVENT \<rparr>) \<and> (True::\<bool>))))) then
		(dummy0RANGE)
		else
		(undefined))))) ) then
			(
		if ((\<exists> (dummy0RANGE :: FMU)  . ((( (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) ))) \<longrightarrow> (\<comment>\<open>Transform a VDM `=` expression into an `eq_FMU` call\<close>
	(eq_FMU dummy0RANGE   (((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) name))\<lparr>mode\<^sub>F\<^sub>M\<^sub>U := FMUMode.U_EVENT \<rparr>) \<and> (True::\<bool>))))) then
		(dummy0RANGE)
		else
		(undefined))
		 else
			undefined
		)
		) 
		(truecnst )))\<rparr>\<rparr>"

	
	
\<comment>\<open>VDM source: postStepMode: (Importer * Importer * set1 of (Name) -> bool)
	postStepMode(I, oldImporter, fmus) ==
(ImporterNotAffected(oldImporter, I) and (preCoSimulationStep((I.scenario), (I.time)) and (fmusNotAffected((rng (fmus <-: ((I.scenario).fmus))), (rng (fmus <-: ((oldImporter.scenario).fmus)))) and let relevantFMUs:set of (FMU) = (rng (fmus <: ((I.scenario).fmus))) in assertFMUMode(relevantFMUs, {<STEP>}))))
	pre (pre_ImporterNotAffected(oldImporter, I) and (pre_preCoSimulationStep((I.scenario), (I.time)) and (pre_fmusNotAffected((rng (fmus <-: ((I.scenario).fmus))), (rng (fmus <-: ((oldImporter.scenario).fmus)))) and let relevantFMUs:set of (FMU) = (rng (fmus <: ((I.scenario).fmus))) in pre_assertFMUMode(relevantFMUs, {<STEP>}))))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1281:5\<close>

\<comment>\<open>VDM source: pre_postStepMode: (Importer * Importer * set1 of (Name) +> bool)
	pre_postStepMode(I, oldImporter, fmus) ==
(pre_ImporterNotAffected(oldImporter, I) and (pre_preCoSimulationStep((I.scenario), (I.time)) and (pre_fmusNotAffected((rng (fmus <-: ((I.scenario).fmus))), (rng (fmus <-: ((oldImporter.scenario).fmus)))) and let relevantFMUs:set of (FMU) = (rng (fmus <: ((I.scenario).fmus))) in pre_assertFMUMode(relevantFMUs, {<STEP>}))))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1290:9\<close>
definition
	pre_postStepMode :: "Importer \<Rightarrow> Importer \<Rightarrow> Name VDMSet1 \<Rightarrow> bool"
where
	"pre_postStepMode I   oldImporter   fmus \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `pre_postStepMode` specification.\<close>
		(inv_Importer I  \<and>  inv_Importer oldImporter  \<and>  (inv_VDMSet1' (inv_Name) fmus))  \<and> 
		\<comment>\<open>User defined body of pre_postStepMode.\<close>
		((pre_ImporterNotAffected oldImporter   I) \<and> ((pre_preCoSimulationStep (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)   (time\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) \<and> ((pre_fmusNotAffected (rng (fmus -\<triangleleft> (fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I))))   (rng (fmus -\<triangleleft> (fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r oldImporter))))) \<and> (
		let 
(relevantFMUs::FMU VDMSet) = (rng (fmus \<triangleleft> (fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I))))
		in
			(if ((inv_VDMSet' inv_FMU  relevantFMUs)) then
			(pre_assertFMUMode relevantFMUs   {FMUMode.U_STEP })
		 else
			undefined
		)
		))))"


\<comment>\<open>VDM source: post_postStepMode: (Importer * Importer * set1 of (Name) * bool +> bool)
	post_postStepMode(I, oldImporter, fmus, RESULT) ==
null\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1281:5\<close>
definition
	post_postStepMode :: "Importer \<Rightarrow> Importer \<Rightarrow> Name VDMSet1 \<Rightarrow> bool \<Rightarrow> bool"
where
	"post_postStepMode I   oldImporter   fmus   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_postStepMode` specification.\<close>
		(inv_Importer I  \<and>  inv_Importer oldImporter  \<and>  (inv_VDMSet1' (inv_Name) fmus)  \<and>  (inv_bool RESULT))"

definition
	postStepMode :: "Importer \<Rightarrow> Importer \<Rightarrow> Name VDMSet1 \<Rightarrow> bool"
where
	"postStepMode I   oldImporter   fmus \<equiv> 
	\<comment>\<open>User defined body of postStepMode.\<close>
	((ImporterNotAffected oldImporter   I) \<and> ((preCoSimulationStep (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)   (time\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) \<and> ((fmusNotAffected (rng (fmus -\<triangleleft> (fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I))))   (rng (fmus -\<triangleleft> (fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r oldImporter))))) \<and> (
		let 
(relevantFMUs::FMU VDMSet) = (rng (fmus \<triangleleft> (fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I))))
		in
			(if ((inv_VDMSet' inv_FMU  relevantFMUs)) then
			(assertFMUMode relevantFMUs   {FMUMode.U_STEP })
		 else
			undefined
		)
		))))"

	
	
\<comment>\<open>VDM source: enterStepMode: (Importer * set1 of (Name) -> Importer)
	enterStepMode(I, fmus) ==
mu(I, scenario |-> mu((I.scenario), fmus |-> (((I.scenario).fmus) ++ {name |-> mu(((I.scenario).fmus)(name), mode |-> <STEP>, time |-> mk_Time(((((I.scenario).fmus)(name).time).r), 0)) | name in set fmus})), time |-> mk_Time(((I.time).r), 0))
	pre (pre_variablesSynchronized((I.scenario), {<continous>}) and (variablesSynchronized((I.scenario), {<continous>}) and let relevantFMUs:set1 of (FMU) = (rng (fmus <: ((I.scenario).fmus))) in (pre_assertFMUMode(relevantFMUs, {<INIT>, <EVENT>}) and (assertFMUMode(relevantFMUs, {<INIT>, <EVENT>}) and (pre_fmusSynchronized(relevantFMUs) and fmusSynchronized(relevantFMUs))))))
	post (pre_postStepMode(RESULT, I, fmus) and postStepMode(RESULT, I, fmus))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1298:5\<close>

\<comment>\<open>VDM source: pre_enterStepMode: (Importer * set1 of (Name) +> bool)
	pre_enterStepMode(I, fmus) ==
(pre_variablesSynchronized((I.scenario), {<continous>}) and (variablesSynchronized((I.scenario), {<continous>}) and let relevantFMUs:set1 of (FMU) = (rng (fmus <: ((I.scenario).fmus))) in (pre_assertFMUMode(relevantFMUs, {<INIT>, <EVENT>}) and (assertFMUMode(relevantFMUs, {<INIT>, <EVENT>}) and (pre_fmusSynchronized(relevantFMUs) and fmusSynchronized(relevantFMUs))))))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1308:9\<close>
definition
	pre_enterStepMode :: "Importer \<Rightarrow> Name VDMSet1 \<Rightarrow> bool"
where
	"pre_enterStepMode I   fmus \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `pre_enterStepMode` specification.\<close>
		(inv_Importer I  \<and>  (inv_VDMSet1' (inv_Name) fmus))  \<and> 
		\<comment>\<open>User defined body of pre_enterStepMode.\<close>
		((pre_variablesSynchronized (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)   {PortType.U_continous }) \<and> ((variablesSynchronized (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)   {PortType.U_continous }) \<and> (
		let 
(relevantFMUs::FMU VDMSet1) = (rng (fmus \<triangleleft> (fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I))))
		in
			(if ((inv_VDMSet1' inv_FMU  relevantFMUs)) then
			((pre_assertFMUMode relevantFMUs   {FMUMode.U_INIT  , FMUMode.U_EVENT }) \<and> ((assertFMUMode relevantFMUs   {FMUMode.U_INIT  , FMUMode.U_EVENT }) \<and> ((pre_fmusSynchronized relevantFMUs) \<and> (fmusSynchronized relevantFMUs))))
		 else
			undefined
		)
		)))"


\<comment>\<open>VDM source: post_enterStepMode: (Importer * set1 of (Name) * Importer +> bool)
	post_enterStepMode(I, fmus, RESULT) ==
(pre_postStepMode(RESULT, I, fmus) and postStepMode(RESULT, I, fmus))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1317:9\<close>
definition
	post_enterStepMode :: "Importer \<Rightarrow> Name VDMSet1 \<Rightarrow> Importer \<Rightarrow> bool"
where
	"post_enterStepMode I   fmus   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `post_enterStepMode` specification.\<close>
		(inv_Importer I  \<and>  (inv_VDMSet1' (inv_Name) fmus)  \<and>  inv_Importer RESULT)  \<and> 
		\<comment>\<open>User defined body of post_enterStepMode.\<close>
		((pre_postStepMode RESULT   I   fmus) \<and> (postStepMode RESULT   I   fmus))"

definition
	enterStepMode :: "Importer \<Rightarrow> Name VDMSet1 \<Rightarrow> Importer"
where
	"enterStepMode I   fmus \<equiv> 
	\<comment>\<open>User defined body of enterStepMode.\<close>
	(I)\<lparr>scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r := ((scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I))\<lparr>fmus\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r := ((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) \<dagger> (\<comment>\<open>VDM Map comprehension is translated as a lambda-term through mapCompSetBound\<close>
		mapCompSetBound 
		{ name .   ((name \<in>fmus))  } 
		{(((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) name))\<lparr>mode\<^sub>F\<^sub>M\<^sub>U := FMUMode.U_STEP , time\<^sub>F\<^sub>M\<^sub>U := \<lparr>r\<^sub>T\<^sub>i\<^sub>m\<^sub>e = (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U (the(((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) name))))), i\<^sub>T\<^sub>i\<^sub>m\<^sub>e = (0::VDMNat)\<rparr>\<rparr>} 
		((inv_VDMSeq1' (inv_VDMChar))) 
		 (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U FMU))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U FMU)))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U FMU))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U FMU)))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U FMU))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U FMU))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U FMU))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U FMU)))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U FMU))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U FMU)))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U FMU)))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U FMU))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U FMU))) ) 
		(domid ) 
		(
	\<lambda> (dummy0DOMAIN :: Name)   (dummy0RANGE :: FMU) .
		(if ((((inv_VDMSeq1' (inv_VDMChar) dummy0DOMAIN))))  \<and>  (( (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) ))) \<and>  (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U (
		if ((\<exists> (dummy0RANGE :: FMU)  . ((( (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) ))) \<longrightarrow> (\<comment>\<open>Transform a VDM `=` expression into an `eq_FMU` call\<close>
	(eq_FMU dummy0RANGE   (((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) name))\<lparr>mode\<^sub>F\<^sub>M\<^sub>U := FMUMode.U_STEP , time\<^sub>F\<^sub>M\<^sub>U := \<lparr>r\<^sub>T\<^sub>i\<^sub>m\<^sub>e = (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U (the(((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) name))))), i\<^sub>T\<^sub>i\<^sub>m\<^sub>e = (0::VDMNat)\<rparr>\<rparr>) \<and> (True::\<bool>))))) then
		(dummy0RANGE)
		else
		(undefined))))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U (
		if ((\<exists> (dummy0RANGE :: FMU)  . ((( (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) ))) \<longrightarrow> (\<comment>\<open>Transform a VDM `=` expression into an `eq_FMU` call\<close>
	(eq_FMU dummy0RANGE   (((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) name))\<lparr>mode\<^sub>F\<^sub>M\<^sub>U := FMUMode.U_STEP , time\<^sub>F\<^sub>M\<^sub>U := \<lparr>r\<^sub>T\<^sub>i\<^sub>m\<^sub>e = (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U (the(((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) name))))), i\<^sub>T\<^sub>i\<^sub>m\<^sub>e = (0::VDMNat)\<rparr>\<rparr>) \<and> (True::\<bool>))))) then
		(dummy0RANGE)
		else
		(undefined)))))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U (
		if ((\<exists> (dummy0RANGE :: FMU)  . ((( (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) ))) \<longrightarrow> (\<comment>\<open>Transform a VDM `=` expression into an `eq_FMU` call\<close>
	(eq_FMU dummy0RANGE   (((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) name))\<lparr>mode\<^sub>F\<^sub>M\<^sub>U := FMUMode.U_STEP , time\<^sub>F\<^sub>M\<^sub>U := \<lparr>r\<^sub>T\<^sub>i\<^sub>m\<^sub>e = (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U (the(((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) name))))), i\<^sub>T\<^sub>i\<^sub>m\<^sub>e = (0::VDMNat)\<rparr>\<rparr>) \<and> (True::\<bool>))))) then
		(dummy0RANGE)
		else
		(undefined))))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U (
		if ((\<exists> (dummy0RANGE :: FMU)  . ((( (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) ))) \<longrightarrow> (\<comment>\<open>Transform a VDM `=` expression into an `eq_FMU` call\<close>
	(eq_FMU dummy0RANGE   (((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) name))\<lparr>mode\<^sub>F\<^sub>M\<^sub>U := FMUMode.U_STEP , time\<^sub>F\<^sub>M\<^sub>U := \<lparr>r\<^sub>T\<^sub>i\<^sub>m\<^sub>e = (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U (the(((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) name))))), i\<^sub>T\<^sub>i\<^sub>m\<^sub>e = (0::VDMNat)\<rparr>\<rparr>) \<and> (True::\<bool>))))) then
		(dummy0RANGE)
		else
		(undefined)))))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U (
		if ((\<exists> (dummy0RANGE :: FMU)  . ((( (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) ))) \<longrightarrow> (\<comment>\<open>Transform a VDM `=` expression into an `eq_FMU` call\<close>
	(eq_FMU dummy0RANGE   (((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) name))\<lparr>mode\<^sub>F\<^sub>M\<^sub>U := FMUMode.U_STEP , time\<^sub>F\<^sub>M\<^sub>U := \<lparr>r\<^sub>T\<^sub>i\<^sub>m\<^sub>e = (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U (the(((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) name))))), i\<^sub>T\<^sub>i\<^sub>m\<^sub>e = (0::VDMNat)\<rparr>\<rparr>) \<and> (True::\<bool>))))) then
		(dummy0RANGE)
		else
		(undefined))))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U (
		if ((\<exists> (dummy0RANGE :: FMU)  . ((( (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) ))) \<longrightarrow> (\<comment>\<open>Transform a VDM `=` expression into an `eq_FMU` call\<close>
	(eq_FMU dummy0RANGE   (((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) name))\<lparr>mode\<^sub>F\<^sub>M\<^sub>U := FMUMode.U_STEP , time\<^sub>F\<^sub>M\<^sub>U := \<lparr>r\<^sub>T\<^sub>i\<^sub>m\<^sub>e = (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U (the(((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) name))))), i\<^sub>T\<^sub>i\<^sub>m\<^sub>e = (0::VDMNat)\<rparr>\<rparr>) \<and> (True::\<bool>))))) then
		(dummy0RANGE)
		else
		(undefined))))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U (
		if ((\<exists> (dummy0RANGE :: FMU)  . ((( (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) ))) \<longrightarrow> (\<comment>\<open>Transform a VDM `=` expression into an `eq_FMU` call\<close>
	(eq_FMU dummy0RANGE   (((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) name))\<lparr>mode\<^sub>F\<^sub>M\<^sub>U := FMUMode.U_STEP , time\<^sub>F\<^sub>M\<^sub>U := \<lparr>r\<^sub>T\<^sub>i\<^sub>m\<^sub>e = (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U (the(((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) name))))), i\<^sub>T\<^sub>i\<^sub>m\<^sub>e = (0::VDMNat)\<rparr>\<rparr>) \<and> (True::\<bool>))))) then
		(dummy0RANGE)
		else
		(undefined))))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U (
		if ((\<exists> (dummy0RANGE :: FMU)  . ((( (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) ))) \<longrightarrow> (\<comment>\<open>Transform a VDM `=` expression into an `eq_FMU` call\<close>
	(eq_FMU dummy0RANGE   (((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) name))\<lparr>mode\<^sub>F\<^sub>M\<^sub>U := FMUMode.U_STEP , time\<^sub>F\<^sub>M\<^sub>U := \<lparr>r\<^sub>T\<^sub>i\<^sub>m\<^sub>e = (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U (the(((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) name))))), i\<^sub>T\<^sub>i\<^sub>m\<^sub>e = (0::VDMNat)\<rparr>\<rparr>) \<and> (True::\<bool>))))) then
		(dummy0RANGE)
		else
		(undefined)))))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U (
		if ((\<exists> (dummy0RANGE :: FMU)  . ((( (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) ))) \<longrightarrow> (\<comment>\<open>Transform a VDM `=` expression into an `eq_FMU` call\<close>
	(eq_FMU dummy0RANGE   (((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) name))\<lparr>mode\<^sub>F\<^sub>M\<^sub>U := FMUMode.U_STEP , time\<^sub>F\<^sub>M\<^sub>U := \<lparr>r\<^sub>T\<^sub>i\<^sub>m\<^sub>e = (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U (the(((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) name))))), i\<^sub>T\<^sub>i\<^sub>m\<^sub>e = (0::VDMNat)\<rparr>\<rparr>) \<and> (True::\<bool>))))) then
		(dummy0RANGE)
		else
		(undefined))))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U (
		if ((\<exists> (dummy0RANGE :: FMU)  . ((( (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) ))) \<longrightarrow> (\<comment>\<open>Transform a VDM `=` expression into an `eq_FMU` call\<close>
	(eq_FMU dummy0RANGE   (((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) name))\<lparr>mode\<^sub>F\<^sub>M\<^sub>U := FMUMode.U_STEP , time\<^sub>F\<^sub>M\<^sub>U := \<lparr>r\<^sub>T\<^sub>i\<^sub>m\<^sub>e = (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U (the(((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) name))))), i\<^sub>T\<^sub>i\<^sub>m\<^sub>e = (0::VDMNat)\<rparr>\<rparr>) \<and> (True::\<bool>))))) then
		(dummy0RANGE)
		else
		(undefined)))))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U (
		if ((\<exists> (dummy0RANGE :: FMU)  . ((( (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) ))) \<longrightarrow> (\<comment>\<open>Transform a VDM `=` expression into an `eq_FMU` call\<close>
	(eq_FMU dummy0RANGE   (((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) name))\<lparr>mode\<^sub>F\<^sub>M\<^sub>U := FMUMode.U_STEP , time\<^sub>F\<^sub>M\<^sub>U := \<lparr>r\<^sub>T\<^sub>i\<^sub>m\<^sub>e = (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U (the(((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) name))))), i\<^sub>T\<^sub>i\<^sub>m\<^sub>e = (0::VDMNat)\<rparr>\<rparr>) \<and> (True::\<bool>))))) then
		(dummy0RANGE)
		else
		(undefined)))))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U (
		if ((\<exists> (dummy0RANGE :: FMU)  . ((( (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) ))) \<longrightarrow> (\<comment>\<open>Transform a VDM `=` expression into an `eq_FMU` call\<close>
	(eq_FMU dummy0RANGE   (((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) name))\<lparr>mode\<^sub>F\<^sub>M\<^sub>U := FMUMode.U_STEP , time\<^sub>F\<^sub>M\<^sub>U := \<lparr>r\<^sub>T\<^sub>i\<^sub>m\<^sub>e = (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U (the(((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) name))))), i\<^sub>T\<^sub>i\<^sub>m\<^sub>e = (0::VDMNat)\<rparr>\<rparr>) \<and> (True::\<bool>))))) then
		(dummy0RANGE)
		else
		(undefined))))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U (
		if ((\<exists> (dummy0RANGE :: FMU)  . ((( (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) ))) \<longrightarrow> (\<comment>\<open>Transform a VDM `=` expression into an `eq_FMU` call\<close>
	(eq_FMU dummy0RANGE   (((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) name))\<lparr>mode\<^sub>F\<^sub>M\<^sub>U := FMUMode.U_STEP , time\<^sub>F\<^sub>M\<^sub>U := \<lparr>r\<^sub>T\<^sub>i\<^sub>m\<^sub>e = (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U (the(((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) name))))), i\<^sub>T\<^sub>i\<^sub>m\<^sub>e = (0::VDMNat)\<rparr>\<rparr>) \<and> (True::\<bool>))))) then
		(dummy0RANGE)
		else
		(undefined))))) ) then
			(
		if ((\<exists> (dummy0RANGE :: FMU)  . ((( (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) ))) \<longrightarrow> (\<comment>\<open>Transform a VDM `=` expression into an `eq_FMU` call\<close>
	(eq_FMU dummy0RANGE   (((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) name))\<lparr>mode\<^sub>F\<^sub>M\<^sub>U := FMUMode.U_STEP , time\<^sub>F\<^sub>M\<^sub>U := \<lparr>r\<^sub>T\<^sub>i\<^sub>m\<^sub>e = (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U (the(((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) name))))), i\<^sub>T\<^sub>i\<^sub>m\<^sub>e = (0::VDMNat)\<rparr>\<rparr>) \<and> (True::\<bool>))))) then
		(dummy0RANGE)
		else
		(undefined))
		 else
			undefined
		)
		) 
		(truecnst )))\<rparr>, time\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r := \<lparr>r\<^sub>T\<^sub>i\<^sub>m\<^sub>e = (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)), i\<^sub>T\<^sub>i\<^sub>m\<^sub>e = (0::VDMNat)\<rparr>\<rparr>"

	
	
\<comment>\<open>VDM source: preEventMode: (Importer * set of (FMURef) -> bool)
	preEventMode(I, clocks) ==
(preCoSimulationStep((I.scenario), (I.time)) and (((I.fmusWithEvent) union clocks) <> {}))
	pre pre_preCoSimulationStep((I.scenario), (I.time))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1320:5\<close>

\<comment>\<open>VDM source: pre_preEventMode: (Importer * set of (FMURef) +> bool)
	pre_preEventMode(I, clocks) ==
pre_preCoSimulationStep((I.scenario), (I.time))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1325:9\<close>
definition
	pre_preEventMode :: "Importer \<Rightarrow> FMURef VDMSet \<Rightarrow> bool"
where
	"pre_preEventMode I   clocks \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `pre_preEventMode` specification.\<close>
		(inv_Importer I  \<and>  (inv_VDMSet' inv_FMURef  clocks))  \<and> 
		\<comment>\<open>User defined body of pre_preEventMode.\<close>
		(pre_preCoSimulationStep (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)   (time\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I))"


\<comment>\<open>VDM source: post_preEventMode: (Importer * set of (FMURef) * bool +> bool)
	post_preEventMode(I, clocks, RESULT) ==
null\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1320:5\<close>
definition
	post_preEventMode :: "Importer \<Rightarrow> FMURef VDMSet \<Rightarrow> bool \<Rightarrow> bool"
where
	"post_preEventMode I   clocks   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_preEventMode` specification.\<close>
		(inv_Importer I  \<and>  (inv_VDMSet' inv_FMURef  clocks)  \<and>  (inv_bool RESULT))"

definition
	preEventMode :: "Importer \<Rightarrow> FMURef VDMSet \<Rightarrow> bool"
where
	"preEventMode I   clocks \<equiv> 
	\<comment>\<open>User defined body of preEventMode.\<close>
	((preCoSimulationStep (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)   (time\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) \<and> (((fmusWithEvent\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I) \<union> clocks) \<noteq> {}))"

	
	
\<comment>\<open>VDM source: postEventMode: (Importer -> bool)
	postEventMode(I) ==
(preCoSimulationStep((I.scenario), (I.time)) and ((I.fmusWithEvent) = {}))
	pre pre_preCoSimulationStep((I.scenario), (I.time))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1327:5\<close>

\<comment>\<open>VDM source: pre_postEventMode: (Importer +> bool)
	pre_postEventMode(I) ==
pre_preCoSimulationStep((I.scenario), (I.time))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1332:9\<close>
definition
	pre_postEventMode :: "Importer \<Rightarrow> bool"
where
	"pre_postEventMode I \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `pre_postEventMode` specification.\<close>
		(inv_Importer I)  \<and> 
		\<comment>\<open>User defined body of pre_postEventMode.\<close>
		(pre_preCoSimulationStep (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)   (time\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I))"


\<comment>\<open>VDM source: post_postEventMode: (Importer * bool +> bool)
	post_postEventMode(I, RESULT) ==
null\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1327:5\<close>
definition
	post_postEventMode :: "Importer \<Rightarrow> bool \<Rightarrow> bool"
where
	"post_postEventMode I   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_postEventMode` specification.\<close>
		(inv_Importer I  \<and>  (inv_bool RESULT))"

definition
	postEventMode :: "Importer \<Rightarrow> bool"
where
	"postEventMode I \<equiv> 
	\<comment>\<open>User defined body of postEventMode.\<close>
	((preCoSimulationStep (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)   (time\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) \<and> ((fmusWithEvent\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I) = {}))"

	
	
\<comment>\<open>VDM source: activateClocks: (Importer * seq of (FMURef) -> Importer)
	activateClocks(I, clocks) ==
(if (clocks = [])
then I
else let clock:FMURef = (hd clocks), I1:Importer = setClock(I, ((I.scenario).fmus)((clock.name)), (clock.ref), true) in activateClocks(I1, (tl clocks)))
	pre let clockSet:set of (FMURef) = (elems clocks) in ((clockSet subset ((I.readyClocks) inter (I.relevantInputClocks))) and let fmusOfClocks:set of (FMU) = {((I.scenario).fmus)((clock.name)) | clock in set clockSet & ((clock.name) in set (dom ((I.scenario).fmus)))} in (pre_assertFMUMode(fmusOfClocks, {<EVENT>}) and (assertFMUMode(fmusOfClocks, {<EVENT>}) and ((clocks <> []) => let clock:FMURef = (hd clocks) in (((clock.name) in set (dom ((I.scenario).fmus))) and (pre_setClock(I, ((I.scenario).fmus)((clock.name)), (clock.ref), true) and let I1:Importer = setClock(I, ((I.scenario).fmus)((clock.name)), (clock.ref), true) in pre_activateClocks(I1, (tl clocks))))))))
	post let clockSet:set of (FMURef) = (elems clocks) in ((clockSet subset (RESULT.activeClocks)) and (((clockSet <> {}) => (not (clockSet subset (RESULT.readyClocks)))) and (((clockSet <> {}) => (not (clockSet subset (RESULT.relevantInputClocks)))) and let fmusOfClocks:set of (FMU) = {((RESULT.scenario).fmus)((clock.name)) | clock in set clockSet} in (pre_assertFMUMode(fmusOfClocks, {<EVENT>}) and assertFMUMode(fmusOfClocks, {<EVENT>})))))
	measure (len clocks)\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1339:5\<close>

\<comment>\<open>VDM source: pre_activateClocks: (Importer * seq of (FMURef) +> bool)
	pre_activateClocks(I, clocks) ==
let clockSet:set of (FMURef) = (elems clocks) in ((clockSet subset ((I.readyClocks) inter (I.relevantInputClocks))) and let fmusOfClocks:set of (FMU) = {((I.scenario).fmus)((clock.name)) | clock in set clockSet & ((clock.name) in set (dom ((I.scenario).fmus)))} in (pre_assertFMUMode(fmusOfClocks, {<EVENT>}) and (assertFMUMode(fmusOfClocks, {<EVENT>}) and ((clocks <> []) => let clock:FMURef = (hd clocks) in (((clock.name) in set (dom ((I.scenario).fmus))) and (pre_setClock(I, ((I.scenario).fmus)((clock.name)), (clock.ref), true) and let I1:Importer = setClock(I, ((I.scenario).fmus)((clock.name)), (clock.ref), true) in pre_activateClocks(I1, (tl clocks))))))))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1347:9\<close>
definition
	pre_activateClocks :: "Importer \<Rightarrow> FMURef VDMSeq \<Rightarrow> bool"
where
	"pre_activateClocks I   clocks \<equiv> 
	\<comment>\<open>Implicitly defined type invariant checks for  `pre_activateClocks` specification.\<close>
	(inv_Importer I  \<and>  (inv_VDMSeq' inv_FMURef  clocks))  \<and> 
	\<comment>\<open>User defined body of pre_activateClocks.\<close>
	(
		let 
(clockSet::FMURef VDMSet) = (elems clocks)
		in
			(if ((inv_VDMSet' inv_FMURef  clockSet)) then
			((clockSet \<subseteq> ((readyClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I) \<inter> (relevantInputClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I))) \<and> (
		let 
(fmusOfClocks::FMU VDMSet) = { ((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) (name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f clock)) | clock .  ((clock \<in>clockSet))  \<and> ((name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f clock) \<in> (dom (fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)))) }
		in
			(if ((inv_VDMSet' inv_FMU  fmusOfClocks)) then
			((pre_assertFMUMode fmusOfClocks   {FMUMode.U_EVENT }) \<and> ((assertFMUMode fmusOfClocks   {FMUMode.U_EVENT }) \<and> ((clocks \<noteq> []) \<longrightarrow> (
		let 
(clock::FMURef) = (hd clocks)
		in
			(if (inv_FMURef clock) then
			(((name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f clock) \<in> (dom (fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)))) \<and> ((pre_setClock I   ((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) (name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f clock))   (ref\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f clock)   (True::\<bool>)) \<and> (
		let 
(I1::Importer) = (setClock I   ((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) (name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f clock))   (ref\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f clock)   (True::\<bool>))
		in
			(if (inv_Importer I1) then
			(pre_activateClocks I1   (tl clocks))
		 else
			undefined
		)
		)))
		 else
			undefined
		)
		))))
		 else
			undefined
		)
		))
		 else
			undefined
		)
		)"


\<comment>\<open>VDM source: post_activateClocks: (Importer * seq of (FMURef) * Importer +> bool)
	post_activateClocks(I, clocks, RESULT) ==
let clockSet:set of (FMURef) = (elems clocks) in ((clockSet subset (RESULT.activeClocks)) and (((clockSet <> {}) => (not (clockSet subset (RESULT.readyClocks)))) and (((clockSet <> {}) => (not (clockSet subset (RESULT.relevantInputClocks)))) and let fmusOfClocks:set of (FMU) = {((RESULT.scenario).fmus)((clock.name)) | clock in set clockSet} in (pre_assertFMUMode(fmusOfClocks, {<EVENT>}) and assertFMUMode(fmusOfClocks, {<EVENT>})))))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1363:9\<close>
definition
	post_activateClocks :: "Importer \<Rightarrow> FMURef VDMSeq \<Rightarrow> Importer \<Rightarrow> bool"
where
	"post_activateClocks I   clocks   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `post_activateClocks` specification.\<close>
		(inv_Importer I  \<and>  (inv_VDMSeq' inv_FMURef  clocks)  \<and>  inv_Importer RESULT)  \<and> 
		\<comment>\<open>User defined body of post_activateClocks.\<close>
		(
		let 
(clockSet::FMURef VDMSet) = (elems clocks)
		in
			(if ((inv_VDMSet' inv_FMURef  clockSet)) then
			((clockSet \<subseteq> (activeClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r RESULT)) \<and> (((clockSet \<noteq> {}) \<longrightarrow> (\<not> (clockSet \<subseteq> (readyClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r RESULT)))) \<and> (((clockSet \<noteq> {}) \<longrightarrow> (\<not> (clockSet \<subseteq> (relevantInputClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r RESULT)))) \<and> (
		let 
(fmusOfClocks::FMU VDMSet) = { ((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r RESULT)) (name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f clock)) | clock .  ((clock \<in>clockSet))  }
		in
			(if ((inv_VDMSet' inv_FMU  fmusOfClocks)) then
			((pre_assertFMUMode fmusOfClocks   {FMUMode.U_EVENT }) \<and> (assertFMUMode fmusOfClocks   {FMUMode.U_EVENT }))
		 else
			undefined
		)
		))))
		 else
			undefined
		)
		)"

fun
	activateClocks :: "Importer \<Rightarrow> FMURef VDMSeq \<Rightarrow> Importer"
where
	"activateClocks I   clocks = 
	\<comment>\<open>User defined body of activateClocks.\<close>
	(
		if ((clocks = [])) then
		(I)
		else
		((
		let 
(clock::FMURef) = (hd clocks)
		;
		
(I1::Importer) = (setClock I   ((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) (name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f clock))   (ref\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f clock)   (True::\<bool>))
		in
			(if (inv_FMURef clock)
	 \<and> 
	(inv_Importer I1) then
			(activateClocks I1   (tl clocks))
		 else
			undefined
		)
		)))"

	
	
\<comment>\<open>VDM source: eventClockActions: (set of (FMURef) * set of (FMURef) -> set of (Action))
	eventClockActions(relevantInputClocks, relevantOutputClocks) ==
let queryClockActions:set of (Action) = {mk_Action(<getC>, (clock.name), (clock.ref)) | clock in set relevantOutputClocks}, setClockActions:set of (Action) = {mk_Action(<setC>, (clock.name), (clock.ref)) | clock in set relevantInputClocks} in (queryClockActions union setClockActions)
	pre ((relevantInputClocks inter relevantOutputClocks) = {})
	post ((card RESULT) = ((card relevantInputClocks) + (card relevantOutputClocks)))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1373:1\<close>

\<comment>\<open>VDM source: pre_eventClockActions: (set of (FMURef) * set of (FMURef) +> bool)
	pre_eventClockActions(relevantInputClocks, relevantOutputClocks) ==
((relevantInputClocks inter relevantOutputClocks) = {})\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1378:52\<close>
definition
	pre_eventClockActions :: "FMURef VDMSet \<Rightarrow> FMURef VDMSet \<Rightarrow> bool"
where
	"pre_eventClockActions relevantInputClocks   relevantOutputClocks \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `pre_eventClockActions` specification.\<close>
		((inv_VDMSet' inv_FMURef  relevantInputClocks)  \<and>  (inv_VDMSet' inv_FMURef  relevantOutputClocks))  \<and> 
		\<comment>\<open>User defined body of pre_eventClockActions.\<close>
		((relevantInputClocks \<inter> relevantOutputClocks) = {})"


\<comment>\<open>VDM source: post_eventClockActions: (set of (FMURef) * set of (FMURef) * set of (Action) +> bool)
	post_eventClockActions(relevantInputClocks, relevantOutputClocks, RESULT) ==
((card RESULT) = ((card relevantInputClocks) + (card relevantOutputClocks)))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1379:18\<close>
definition
	post_eventClockActions :: "FMURef VDMSet \<Rightarrow> FMURef VDMSet \<Rightarrow> Action VDMSet \<Rightarrow> bool"
where
	"post_eventClockActions relevantInputClocks   relevantOutputClocks   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `post_eventClockActions` specification.\<close>
		((inv_VDMSet' inv_FMURef  relevantInputClocks)  \<and>  (inv_VDMSet' inv_FMURef  relevantOutputClocks)  \<and>  (inv_VDMSet' inv_Action  RESULT))  \<and> 
		\<comment>\<open>User defined body of post_eventClockActions.\<close>
		((vdm_card RESULT) = ((vdm_card relevantInputClocks) + (vdm_card relevantOutputClocks)))"

definition
	eventClockActions :: "FMURef VDMSet \<Rightarrow> FMURef VDMSet \<Rightarrow> Action VDMSet"
where
	"eventClockActions relevantInputClocks   relevantOutputClocks \<equiv> 
	\<comment>\<open>User defined body of eventClockActions.\<close>
	(
		let 
(queryClockActions::Action VDMSet) = { \<lparr>actionType\<^sub>A\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n = U_getC ActionType.U_getC , fmu\<^sub>A\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n = (name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f clock), port\<^sub>A\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n = (ref\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f clock)\<rparr> | clock .  ((clock \<in>relevantOutputClocks))  }
		;
		
(setClockActions::Action VDMSet) = { \<lparr>actionType\<^sub>A\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n = U_setC ActionType.U_setC , fmu\<^sub>A\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n = (name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f clock), port\<^sub>A\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n = (ref\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f clock)\<rparr> | clock .  ((clock \<in>relevantInputClocks))  }
		in
			(if ((inv_VDMSet' inv_Action  queryClockActions))
	 \<and> 
	((inv_VDMSet' inv_Action  setClockActions)) then
			(queryClockActions \<union> setClockActions)
		 else
			undefined
		)
		)"

	
	
\<comment>\<open>VDM source: selectAction: (Importer -> Action)
	selectAction(I) ==
let fmus:map (Name) to (FMU) = ((I.scenario).fmus), clockActions:set of (Action) = eventClockActions((I.relevantInputClocks), (I.relevantOutputClocks)), enableClockActions:set of (Action) = {action | action in set clockActions & (pre_isActionEnabled(I, action) and isActionEnabled(I, action))} in (if (enableClockActions <> {})
then let clockAction in set enableClockActions in clockAction
else let portActions:set of (Action) = ({mk_Action(<set>, (inputRef.name), (inputRef.ref)) | inputRef in set ((I.activeEquations) \ (I.calculatedEquations)) & ((inputRef.ref) in set {(inputVar.ref) | inputVar in set ((fmus((inputRef.name)).io).LFinput)})} union {mk_Action(<get>, (outputRef.name), (outputRef.ref)) | outputRef in set ((I.activeEquations) \ (I.calculatedEquations)) & ((outputRef.ref) in set {(outputVar.ref) | outputVar in set ((fmus((outputRef.name)).io).LFoutput)})}) in let portAction in set {action | action in set portActions & (pre_isActionEnabled(I, action) and isActionEnabled(I, action))} in portAction)
	pre ((((I.activeEquations) \ (I.calculatedEquations)) <> {}) and pre_eventClockActions((I.relevantInputClocks), (I.relevantOutputClocks)))
	post (((RESULT.actionType) <> <step>) and ((((RESULT.actionType) in set {<getC>, <setC>}) => (((I.relevantOutputClocks) union (I.relevantInputClocks)) <> {})) and (((RESULT.actionType) not in set {<getC>, <setC>}) => (((I.relevantOutputClocks) union (I.relevantInputClocks)) = {}))))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1386:1\<close>

\<comment>\<open>VDM source: pre_selectAction: (Importer +> bool)
	pre_selectAction(I) ==
((((I.activeEquations) \ (I.calculatedEquations)) <> {}) and pre_eventClockActions((I.relevantInputClocks), (I.relevantOutputClocks)))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1403:9\<close>
definition
	pre_selectAction :: "Importer \<Rightarrow> bool"
where
	"pre_selectAction I \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `pre_selectAction` specification.\<close>
		(inv_Importer I)  \<and> 
		\<comment>\<open>User defined body of pre_selectAction.\<close>
		((((activeEquations\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I) - (calculatedEquations\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) \<noteq> {}) \<and> (pre_eventClockActions (relevantInputClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)   (relevantOutputClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)))"


\<comment>\<open>VDM source: post_selectAction: (Importer * Action +> bool)
	post_selectAction(I, RESULT) ==
(((RESULT.actionType) <> <step>) and ((((RESULT.actionType) in set {<getC>, <setC>}) => (((I.relevantOutputClocks) union (I.relevantInputClocks)) <> {})) and (((RESULT.actionType) not in set {<getC>, <setC>}) => (((I.relevantOutputClocks) union (I.relevantInputClocks)) = {}))))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1406:9\<close>
definition
	post_selectAction :: "Importer \<Rightarrow> Action \<Rightarrow> bool"
where
	"post_selectAction I   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `post_selectAction` specification.\<close>
		(inv_Importer I  \<and>  inv_Action RESULT)  \<and> 
		\<comment>\<open>User defined body of post_selectAction.\<close>
		(((actionType\<^sub>A\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n RESULT) \<noteq> ActionType.U_step ) \<and> ((((actionType\<^sub>A\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n RESULT) \<in> {ActionType.U_getC  , ActionType.U_setC }) \<longrightarrow> (((relevantOutputClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I) \<union> (relevantInputClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) \<noteq> {})) \<and> (((actionType\<^sub>A\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n RESULT) \<notin> {ActionType.U_getC  , ActionType.U_setC }) \<longrightarrow> (((relevantOutputClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I) \<union> (relevantInputClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) = {}))))"

definition
	selectAction :: "Importer \<Rightarrow> Action"
where
	"selectAction I \<equiv> 
	\<comment>\<open>User defined body of selectAction.\<close>
	(
		let 
(fmus::(Name \<rightharpoonup> FMU)) = (fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I))
		;
		
(clockActions::Action VDMSet) = (eventClockActions (relevantInputClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)   (relevantOutputClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I))
		;
		
(enableClockActions::Action VDMSet) = { action .   ((action \<in>clockActions))  \<and> ((pre_isActionEnabled I   action) \<and> (isActionEnabled I   action)) }
		in
			(if ((inv_Map ((inv_VDMSeq1' (inv_VDMChar))) inv_FMU  fmus))
	 \<and> 
	((inv_VDMSet' inv_Action  clockActions))
	 \<and> 
	((inv_VDMSet' inv_Action  enableClockActions)) then
			(
		if ((enableClockActions \<noteq> {})) then
		((
		SOME (dummy0::Action) .(dummy0 \<in> { clockAction .   ((clockAction \<in>enableClockActions))  })))
		else
		((
		let 
(portActions::Action VDMSet) = ({ \<lparr>actionType\<^sub>A\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n = U_set ActionType.U_set , fmu\<^sub>A\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n = (name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f inputRef), port\<^sub>A\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n = (ref\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f inputRef)\<rparr> | inputRef .  ((inputRef \<in>((activeEquations\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I) - (calculatedEquations\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I))))  \<and> ((ref\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f inputRef) \<in> { (ref\<^sub>V\<^sub>a\<^sub>r\<^sub>i\<^sub>a\<^sub>b\<^sub>l\<^sub>e inputVar) | inputVar .  ((inputVar \<in>(LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U (the((fmus (name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f inputRef))))))))  }) } \<union> { \<lparr>actionType\<^sub>A\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n = U_get ActionType.U_get , fmu\<^sub>A\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n = (name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f outputRef), port\<^sub>A\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n = (ref\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f outputRef)\<rparr> | outputRef .  ((outputRef \<in>((activeEquations\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I) - (calculatedEquations\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I))))  \<and> ((ref\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f outputRef) \<in> { (ref\<^sub>V\<^sub>a\<^sub>r\<^sub>i\<^sub>a\<^sub>b\<^sub>l\<^sub>e outputVar) | outputVar .  ((outputVar \<in>(LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U (the((fmus (name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f outputRef))))))))  }) })
		in
			(if ((inv_VDMSet' inv_Action  portActions)) then
			(
		SOME (dummy0::Action) .(dummy0 \<in> { portAction .   ((portAction \<in>{ action .   ((action \<in>portActions))  \<and> ((pre_isActionEnabled I   action) \<and> (isActionEnabled I   action)) }))  }))
		 else
			undefined
		)
		)))
		 else
			undefined
		)
		)"

	
	
\<comment>\<open>VDM source: solveSystemOfEquations: (Importer -> Importer)
	solveSystemOfEquations(I) ==
(if (((I.activeEquations) \ (I.calculatedEquations)) = {})
then I
else let action:Action = selectAction(I) in solveSystemOfEquations(runAction(I, action)))
	pre ((((I.activeEquations) \ (I.calculatedEquations)) <> {}) => (pre_selectAction(I) and let action:Action = selectAction(I) in (pre_runAction(I, action) and pre_solveSystemOfEquations(runAction(I, action)))))
	post (((RESULT.activeEquations) \ (RESULT.calculatedEquations)) = {})
	measure ((card (I.readyEquations)) + (card ((I.activeEquations) \ (I.calculatedEquations))))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1417:5\<close>

\<comment>\<open>VDM source: pre_solveSystemOfEquations: (Importer +> bool)
	pre_solveSystemOfEquations(I) ==
((((I.activeEquations) \ (I.calculatedEquations)) <> {}) => (pre_selectAction(I) and let action:Action = selectAction(I) in (pre_runAction(I, action) and pre_solveSystemOfEquations(runAction(I, action)))))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1424:59\<close>
definition
	pre_solveSystemOfEquations :: "Importer \<Rightarrow> bool"
where
	"pre_solveSystemOfEquations I \<equiv> 
	\<comment>\<open>Implicitly defined type invariant checks for  `pre_solveSystemOfEquations` specification.\<close>
	(inv_Importer I)  \<and> 
	\<comment>\<open>User defined body of pre_solveSystemOfEquations.\<close>
	((((activeEquations\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I) - (calculatedEquations\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) \<noteq> {}) \<longrightarrow> ((pre_selectAction I) \<and> (
		let 
(action::Action) = (selectAction I)
		in
			(if (inv_Action action) then
			((pre_runAction I   action) \<and> (pre_solveSystemOfEquations (runAction I   action)))
		 else
			undefined
		)
		)))"


\<comment>\<open>VDM source: post_solveSystemOfEquations: (Importer * Importer +> bool)
	post_solveSystemOfEquations(I, RESULT) ==
(((RESULT.activeEquations) \ (RESULT.calculatedEquations)) = {})\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1430:61\<close>
definition
	post_solveSystemOfEquations :: "Importer \<Rightarrow> Importer \<Rightarrow> bool"
where
	"post_solveSystemOfEquations I   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `post_solveSystemOfEquations` specification.\<close>
		(inv_Importer I  \<and>  inv_Importer RESULT)  \<and> 
		\<comment>\<open>User defined body of post_solveSystemOfEquations.\<close>
		(((activeEquations\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r RESULT) - (calculatedEquations\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r RESULT)) = {})"

fun
	solveSystemOfEquations :: "Importer \<Rightarrow> Importer"
where
	"solveSystemOfEquations I = 
	\<comment>\<open>User defined body of solveSystemOfEquations.\<close>
	(
		if ((((activeEquations\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I) - (calculatedEquations\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) = {})) then
		(I)
		else
		((
		let 
(action::Action) = (selectAction I)
		in
			(if (inv_Action action) then
			(solveSystemOfEquations (runAction I   action))
		 else
			undefined
		)
		)))"

	
	
\<comment>\<open>VDM source: timeAdvanced: (set1 of (FMU) * set1 of (FMU) * bool -> bool)
	timeAdvanced(newFMUs, oldFMUs, discreteTime) ==
(forall m' in set newFMUs & (exists1 m in set oldFMUs & (((m.name) = (m'.name)) and (((m.time) <= (m'.time)) and ((discreteTime => (((((m.time).i) + 1) = ((m'.time).i)) and (((m.time).r) = ((m'.time).r)))) and ((not discreteTime) => ((((m.time).i) = ((m'.time).i)) and (((m.time).r) <= ((m'.time).r)))))))))
	pre (pre_sameSetOfFMUs(newFMUs, oldFMUs) and sameSetOfFMUs(newFMUs, oldFMUs))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1433:5\<close>

\<comment>\<open>VDM source: pre_timeAdvanced: (set1 of (FMU) * set1 of (FMU) * bool +> bool)
	pre_timeAdvanced(newFMUs, oldFMUs, discreteTime) ==
(pre_sameSetOfFMUs(newFMUs, oldFMUs) and sameSetOfFMUs(newFMUs, oldFMUs))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1442:9\<close>
definition
	pre_timeAdvanced :: "FMU VDMSet1 \<Rightarrow> FMU VDMSet1 \<Rightarrow> bool \<Rightarrow> bool"
where
	"pre_timeAdvanced newFMUs   oldFMUs   discreteTime \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `pre_timeAdvanced` specification.\<close>
		((inv_VDMSet1' inv_FMU  newFMUs)  \<and>  (inv_VDMSet1' inv_FMU  oldFMUs)  \<and>  (inv_bool discreteTime))  \<and> 
		\<comment>\<open>User defined body of pre_timeAdvanced.\<close>
		((pre_sameSetOfFMUs newFMUs   oldFMUs) \<and> (sameSetOfFMUs newFMUs   oldFMUs))"


\<comment>\<open>VDM source: post_timeAdvanced: (set1 of (FMU) * set1 of (FMU) * bool * bool +> bool)
	post_timeAdvanced(newFMUs, oldFMUs, discreteTime, RESULT) ==
null\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1433:5\<close>
definition
	post_timeAdvanced :: "FMU VDMSet1 \<Rightarrow> FMU VDMSet1 \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool"
where
	"post_timeAdvanced newFMUs   oldFMUs   discreteTime   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_timeAdvanced` specification.\<close>
		((inv_VDMSet1' inv_FMU  newFMUs)  \<and>  (inv_VDMSet1' inv_FMU  oldFMUs)  \<and>  (inv_bool discreteTime)  \<and>  (inv_bool RESULT))"

definition
	timeAdvanced :: "FMU VDMSet1 \<Rightarrow> FMU VDMSet1 \<Rightarrow> bool \<Rightarrow> bool"
where
	"timeAdvanced newFMUs   oldFMUs   discreteTime \<equiv> 
	\<comment>\<open>User defined body of timeAdvanced.\<close>
	(\<forall> m' \<in> newFMUs  . (\<exists>! m \<in> oldFMUs  . (((name\<^sub>F\<^sub>M\<^sub>U m) = (name\<^sub>F\<^sub>M\<^sub>U m')) \<and> (\<comment>\<open>Transform a VDM `<` expression into an `ord_Time` call\<close>
	(ord_Time (time\<^sub>F\<^sub>M\<^sub>U m)   (time\<^sub>F\<^sub>M\<^sub>U m')) \<or> 
	\<comment>\<open>Transform a VDM `=` expression into an `eq_Time` call\<close>
	(eq_Time (time\<^sub>F\<^sub>M\<^sub>U m)   (time\<^sub>F\<^sub>M\<^sub>U m')) \<and> ((discreteTime \<longrightarrow> ((((i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U m)) + (1::VDMNat1)) = (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U m'))) \<and> ((r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U m)) = (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U m'))))) \<and> ((\<not> discreteTime) \<longrightarrow> (((i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U m)) = (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U m'))) \<and> ((r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U m)) \<le> (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U m'))))))))))"

	
	
\<comment>\<open>VDM source: eventSolved: (Importer * set1 of (FMU) * set1 of (FMU) -> bool)
	eventSolved(I, newFmus, oldFmus) ==
(assertFMUMode(newFmus, {<EVENT>}) and (timeAdvanced(newFmus, oldFmus, true) and ((((I.activeEquations) \ (I.calculatedEquations)) = {}) and (((I.relevantInputClocks) union (I.relevantOutputClocks)) = {}))))
	pre (pre_timeAdvanced(newFmus, oldFmus, true) and (pre_assertFMUMode(newFmus, {<EVENT>}) and (pre_sameSetOfFMUs(newFmus, oldFmus) and sameSetOfFMUs(newFmus, oldFmus))))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1445:5\<close>

\<comment>\<open>VDM source: pre_eventSolved: (Importer * set1 of (FMU) * set1 of (FMU) +> bool)
	pre_eventSolved(I, newFmus, oldFmus) ==
(pre_timeAdvanced(newFmus, oldFmus, true) and (pre_assertFMUMode(newFmus, {<EVENT>}) and (pre_sameSetOfFMUs(newFmus, oldFmus) and sameSetOfFMUs(newFmus, oldFmus))))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1453:13\<close>
definition
	pre_eventSolved :: "Importer \<Rightarrow> FMU VDMSet1 \<Rightarrow> FMU VDMSet1 \<Rightarrow> bool"
where
	"pre_eventSolved I   newFmus   oldFmus \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `pre_eventSolved` specification.\<close>
		(inv_Importer I  \<and>  (inv_VDMSet1' inv_FMU  newFmus)  \<and>  (inv_VDMSet1' inv_FMU  oldFmus))  \<and> 
		\<comment>\<open>User defined body of pre_eventSolved.\<close>
		((pre_timeAdvanced newFmus   oldFmus   (True::\<bool>)) \<and> ((pre_assertFMUMode newFmus   {FMUMode.U_EVENT }) \<and> ((pre_sameSetOfFMUs newFmus   oldFmus) \<and> (sameSetOfFMUs newFmus   oldFmus))))"


\<comment>\<open>VDM source: post_eventSolved: (Importer * set1 of (FMU) * set1 of (FMU) * bool +> bool)
	post_eventSolved(I, newFmus, oldFmus, RESULT) ==
null\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1445:5\<close>
definition
	post_eventSolved :: "Importer \<Rightarrow> FMU VDMSet1 \<Rightarrow> FMU VDMSet1 \<Rightarrow> bool \<Rightarrow> bool"
where
	"post_eventSolved I   newFmus   oldFmus   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_eventSolved` specification.\<close>
		(inv_Importer I  \<and>  (inv_VDMSet1' inv_FMU  newFmus)  \<and>  (inv_VDMSet1' inv_FMU  oldFmus)  \<and>  (inv_bool RESULT))"

definition
	eventSolved :: "Importer \<Rightarrow> FMU VDMSet1 \<Rightarrow> FMU VDMSet1 \<Rightarrow> bool"
where
	"eventSolved I   newFmus   oldFmus \<equiv> 
	\<comment>\<open>User defined body of eventSolved.\<close>
	((assertFMUMode newFmus   {FMUMode.U_EVENT }) \<and> ((timeAdvanced newFmus   oldFmus   (True::\<bool>)) \<and> ((((activeEquations\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I) - (calculatedEquations\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) = {}) \<and> (((relevantInputClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I) \<union> (relevantOutputClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) = {}))))"

	
	
\<comment>\<open>VDM source: updateDiscreteState: (Importer * set1 of (Name) -> Importer)
	updateDiscreteState(I, fmus) ==
let M:Scenario = (I.scenario), res:map (Name) to ((FMU * bool)) = {fmu |-> step_e((M.fmus)(fmu)) | fmu in set fmus}, fmuMap:map (Name) to (FMU) = (((I.scenario).fmus) ++ {fmu |-> (res(fmu).#1) | fmu in set (dom res)}), eventFMUs:set of (Name) = {fmu | fmu in set (dom res) & ((res(fmu).#2) = true)} in mu(I, scenario |-> mu((I.scenario), fmus |-> fmuMap), fmusWithEvent |-> eventFMUs, activeClocks |-> {}, inactiveClocks |-> ((I.inactiveClocks) union (I.activeClocks)), activeEquations |-> {}, readyClocks |-> ((I.inactiveClocks) union (I.activeClocks)), readyEquations |-> (((I.readyEquations) union (I.calculatedEquations)) union (I.activeEquations)), calculatedEquations |-> {}, activeEquations |-> {})
	pre ((fmus subset (dom ((I.scenario).fmus))) and (({pre_step_e(((I.scenario).fmus)(fmu)) | fmu in set fmus} = {true}) and let relevantFMUs:set1 of (FMU) = (rng (fmus <: ((I.scenario).fmus))) in (pre_assertFMUMode(relevantFMUs, {<EVENT>}) and (assertFMUMode(relevantFMUs, {<EVENT>}) and (pre_fmusSynchronized(relevantFMUs) and fmusSynchronized(relevantFMUs))))))
	post let newFmus:set1 of (FMU) = (rng (fmus <: ((RESULT.scenario).fmus))), oldFMUs:set1 of (FMU) = (rng (fmus <: ((I.scenario).fmus))) in (pre_assertFMUMode(newFmus, {<EVENT>}) and (assertFMUMode(newFmus, {<EVENT>}) and (pre_fmusSynchronized(newFmus) and (fmusSynchronized(newFmus) and (pre_timeAdvanced(newFmus, oldFMUs, true) and timeAdvanced(newFmus, oldFMUs, true))))))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1462:5\<close>

\<comment>\<open>VDM source: pre_updateDiscreteState: (Importer * set1 of (Name) +> bool)
	pre_updateDiscreteState(I, fmus) ==
((fmus subset (dom ((I.scenario).fmus))) and (({pre_step_e(((I.scenario).fmus)(fmu)) | fmu in set fmus} = {true}) and let relevantFMUs:set1 of (FMU) = (rng (fmus <: ((I.scenario).fmus))) in (pre_assertFMUMode(relevantFMUs, {<EVENT>}) and (assertFMUMode(relevantFMUs, {<EVENT>}) and (pre_fmusSynchronized(relevantFMUs) and fmusSynchronized(relevantFMUs))))))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1482:9\<close>
definition
	pre_updateDiscreteState :: "Importer \<Rightarrow> Name VDMSet1 \<Rightarrow> bool"
where
	"pre_updateDiscreteState I   fmus \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `pre_updateDiscreteState` specification.\<close>
		(inv_Importer I  \<and>  (inv_VDMSet1' (inv_Name) fmus))  \<and> 
		\<comment>\<open>User defined body of pre_updateDiscreteState.\<close>
		((fmus \<subseteq> (dom (fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)))) \<and> (({ (pre_step_e ((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) fmu)) | fmu .  ((fmu \<in>fmus))  } = {(True::\<bool>)}) \<and> (
		let 
(relevantFMUs::FMU VDMSet1) = (rng (fmus \<triangleleft> (fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I))))
		in
			(if ((inv_VDMSet1' inv_FMU  relevantFMUs)) then
			((pre_assertFMUMode relevantFMUs   {FMUMode.U_EVENT }) \<and> ((assertFMUMode relevantFMUs   {FMUMode.U_EVENT }) \<and> ((pre_fmusSynchronized relevantFMUs) \<and> (fmusSynchronized relevantFMUs))))
		 else
			undefined
		)
		)))"


\<comment>\<open>VDM source: post_updateDiscreteState: (Importer * set1 of (Name) * Importer +> bool)
	post_updateDiscreteState(I, fmus, RESULT) ==
let newFmus:set1 of (FMU) = (rng (fmus <: ((RESULT.scenario).fmus))), oldFMUs:set1 of (FMU) = (rng (fmus <: ((I.scenario).fmus))) in (pre_assertFMUMode(newFmus, {<EVENT>}) and (assertFMUMode(newFmus, {<EVENT>}) and (pre_fmusSynchronized(newFmus) and (fmusSynchronized(newFmus) and (pre_timeAdvanced(newFmus, oldFMUs, true) and timeAdvanced(newFmus, oldFMUs, true))))))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1489:9\<close>
definition
	post_updateDiscreteState :: "Importer \<Rightarrow> Name VDMSet1 \<Rightarrow> Importer \<Rightarrow> bool"
where
	"post_updateDiscreteState I   fmus   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `post_updateDiscreteState` specification.\<close>
		(inv_Importer I  \<and>  (inv_VDMSet1' (inv_Name) fmus)  \<and>  inv_Importer RESULT)  \<and> 
		\<comment>\<open>User defined body of post_updateDiscreteState.\<close>
		(
		let 
(newFmus::FMU VDMSet1) = (rng (fmus \<triangleleft> (fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r RESULT))))
		;
		
(oldFMUs::FMU VDMSet1) = (rng (fmus \<triangleleft> (fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I))))
		in
			(if ((inv_VDMSet1' inv_FMU  newFmus))
	 \<and> 
	((inv_VDMSet1' inv_FMU  oldFMUs)) then
			((pre_assertFMUMode newFmus   {FMUMode.U_EVENT }) \<and> ((assertFMUMode newFmus   {FMUMode.U_EVENT }) \<and> ((pre_fmusSynchronized newFmus) \<and> ((fmusSynchronized newFmus) \<and> ((pre_timeAdvanced newFmus   oldFMUs   (True::\<bool>)) \<and> (timeAdvanced newFmus   oldFMUs   (True::\<bool>)))))))
		 else
			undefined
		)
		)"

definition
	updateDiscreteState :: "Importer \<Rightarrow> Name VDMSet1 \<Rightarrow> Importer"
where
	"updateDiscreteState I   fmus \<equiv> 
	\<comment>\<open>User defined body of updateDiscreteState.\<close>
	(
		let 
(M::Scenario) = (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)
		;
		
(res::(Name \<rightharpoonup> (FMU \<times> bool))) = (\<comment>\<open>VDM Map comprehension is translated as a lambda-term through mapCompSetBound\<close>
		mapCompSetBound 
		{ fmu .   ((fmu \<in>fmus))  } 
		{(step_e ((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o M) fmu))} 
		((inv_VDMSeq1' (inv_VDMChar))) 
		
		( (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U ))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U )))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U ))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U )))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U ))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U ))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U ))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U )))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U ))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U )))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U )))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U ))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U ))) )\<and>
		 (inv_bool )
		) 
		(domid ) 
		(
	\<lambda> (dummy0DOMAIN :: Name)   (dummy0RANGE :: (FMU \<times> bool)) .
		(if ((((inv_VDMSeq1' (inv_VDMChar) dummy0DOMAIN))))  \<and>  ((
		( (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE))))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE))))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE))))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE))))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE))))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))) )\<and>
		 (inv_bool (snd dummy0RANGE))
		))) \<and> 
		( (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U (fst (
		if ((\<exists> (dummy0RANGE :: (FMU \<times> bool))  . (((
		( (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE))))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE))))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE))))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE))))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE))))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))) )\<and>
		 (inv_bool (snd dummy0RANGE))
		))) \<longrightarrow> ((dummy0RANGE = (step_e ((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o M) fmu))) \<and> (True::\<bool>))))) then
		(dummy0RANGE)
		else
		(undefined)))))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U (fst (
		if ((\<exists> (dummy0RANGE :: (FMU \<times> bool))  . (((
		( (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE))))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE))))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE))))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE))))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE))))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))) )\<and>
		 (inv_bool (snd dummy0RANGE))
		))) \<longrightarrow> ((dummy0RANGE = (step_e ((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o M) fmu))) \<and> (True::\<bool>))))) then
		(dummy0RANGE)
		else
		(undefined))))))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U (fst (
		if ((\<exists> (dummy0RANGE :: (FMU \<times> bool))  . (((
		( (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE))))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE))))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE))))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE))))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE))))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))) )\<and>
		 (inv_bool (snd dummy0RANGE))
		))) \<longrightarrow> ((dummy0RANGE = (step_e ((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o M) fmu))) \<and> (True::\<bool>))))) then
		(dummy0RANGE)
		else
		(undefined)))))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U (fst (
		if ((\<exists> (dummy0RANGE :: (FMU \<times> bool))  . (((
		( (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE))))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE))))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE))))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE))))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE))))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))) )\<and>
		 (inv_bool (snd dummy0RANGE))
		))) \<longrightarrow> ((dummy0RANGE = (step_e ((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o M) fmu))) \<and> (True::\<bool>))))) then
		(dummy0RANGE)
		else
		(undefined))))))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U (fst (
		if ((\<exists> (dummy0RANGE :: (FMU \<times> bool))  . (((
		( (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE))))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE))))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE))))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE))))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE))))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))) )\<and>
		 (inv_bool (snd dummy0RANGE))
		))) \<longrightarrow> ((dummy0RANGE = (step_e ((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o M) fmu))) \<and> (True::\<bool>))))) then
		(dummy0RANGE)
		else
		(undefined)))))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U (fst (
		if ((\<exists> (dummy0RANGE :: (FMU \<times> bool))  . (((
		( (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE))))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE))))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE))))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE))))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE))))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))) )\<and>
		 (inv_bool (snd dummy0RANGE))
		))) \<longrightarrow> ((dummy0RANGE = (step_e ((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o M) fmu))) \<and> (True::\<bool>))))) then
		(dummy0RANGE)
		else
		(undefined)))))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U (fst (
		if ((\<exists> (dummy0RANGE :: (FMU \<times> bool))  . (((
		( (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE))))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE))))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE))))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE))))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE))))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))) )\<and>
		 (inv_bool (snd dummy0RANGE))
		))) \<longrightarrow> ((dummy0RANGE = (step_e ((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o M) fmu))) \<and> (True::\<bool>))))) then
		(dummy0RANGE)
		else
		(undefined)))))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U (fst (
		if ((\<exists> (dummy0RANGE :: (FMU \<times> bool))  . (((
		( (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE))))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE))))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE))))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE))))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE))))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))) )\<and>
		 (inv_bool (snd dummy0RANGE))
		))) \<longrightarrow> ((dummy0RANGE = (step_e ((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o M) fmu))) \<and> (True::\<bool>))))) then
		(dummy0RANGE)
		else
		(undefined))))))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U (fst (
		if ((\<exists> (dummy0RANGE :: (FMU \<times> bool))  . (((
		( (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE))))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE))))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE))))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE))))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE))))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))) )\<and>
		 (inv_bool (snd dummy0RANGE))
		))) \<longrightarrow> ((dummy0RANGE = (step_e ((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o M) fmu))) \<and> (True::\<bool>))))) then
		(dummy0RANGE)
		else
		(undefined)))))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U (fst (
		if ((\<exists> (dummy0RANGE :: (FMU \<times> bool))  . (((
		( (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE))))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE))))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE))))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE))))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE))))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))) )\<and>
		 (inv_bool (snd dummy0RANGE))
		))) \<longrightarrow> ((dummy0RANGE = (step_e ((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o M) fmu))) \<and> (True::\<bool>))))) then
		(dummy0RANGE)
		else
		(undefined))))))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U (fst (
		if ((\<exists> (dummy0RANGE :: (FMU \<times> bool))  . (((
		( (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE))))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE))))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE))))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE))))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE))))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))) )\<and>
		 (inv_bool (snd dummy0RANGE))
		))) \<longrightarrow> ((dummy0RANGE = (step_e ((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o M) fmu))) \<and> (True::\<bool>))))) then
		(dummy0RANGE)
		else
		(undefined))))))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U (fst (
		if ((\<exists> (dummy0RANGE :: (FMU \<times> bool))  . (((
		( (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE))))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE))))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE))))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE))))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE))))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))) )\<and>
		 (inv_bool (snd dummy0RANGE))
		))) \<longrightarrow> ((dummy0RANGE = (step_e ((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o M) fmu))) \<and> (True::\<bool>))))) then
		(dummy0RANGE)
		else
		(undefined)))))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U (fst (
		if ((\<exists> (dummy0RANGE :: (FMU \<times> bool))  . (((
		( (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE))))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE))))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE))))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE))))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE))))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))) )\<and>
		 (inv_bool (snd dummy0RANGE))
		))) \<longrightarrow> ((dummy0RANGE = (step_e ((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o M) fmu))) \<and> (True::\<bool>))))) then
		(dummy0RANGE)
		else
		(undefined)))))) )\<and>
		 (inv_bool (snd (
		if ((\<exists> (dummy0RANGE :: (FMU \<times> bool))  . (((
		( (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE))))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE))))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE))))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE))))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE))))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))) )\<and>
		 (inv_bool (snd dummy0RANGE))
		))) \<longrightarrow> ((dummy0RANGE = (step_e ((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o M) fmu))) \<and> (True::\<bool>))))) then
		(dummy0RANGE)
		else
		(undefined))))
		) then
			(
		if ((\<exists> (dummy0RANGE :: (FMU \<times> bool))  . (((
		( (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE))))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE))))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE))))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE))))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE))))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U (fst dummy0RANGE)))) )\<and>
		 (inv_bool (snd dummy0RANGE))
		))) \<longrightarrow> ((dummy0RANGE = (step_e ((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o M) fmu))) \<and> (True::\<bool>))))) then
		(dummy0RANGE)
		else
		(undefined))
		 else
			undefined
		)
		) 
		(truecnst ))
		;
		
(fmuMap::(Name \<rightharpoonup> FMU)) = ((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) \<dagger> (\<comment>\<open>VDM Map comprehension is translated as a lambda-term through mapCompSetBound\<close>
		mapCompSetBound 
		{ fmu .   ((fmu \<in>(dom res)))  } 
		{(fst ((res fmu)))} 
		((inv_VDMSeq1' (inv_VDMChar))) 
		 (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U FMU))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U FMU)))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U FMU))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U FMU)))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U FMU))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U FMU))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U FMU))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U FMU)))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U FMU))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U FMU)))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U FMU)))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U FMU))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U FMU))) ) 
		(domid ) 
		(
	\<lambda> (dummy0DOMAIN :: Name)   (dummy0RANGE :: FMU) .
		(if ((((inv_VDMSeq1' (inv_VDMChar) dummy0DOMAIN))))  \<and>  (( (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) ))) \<and>  (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U (
		if ((\<exists> (dummy0RANGE :: FMU)  . ((( (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) ))) \<longrightarrow> (\<comment>\<open>Transform a VDM `=` expression into an `eq_FMU` call\<close>
	(eq_FMU dummy0RANGE   (fst ((res fmu)))) \<and> (True::\<bool>))))) then
		(dummy0RANGE)
		else
		(undefined))))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U (
		if ((\<exists> (dummy0RANGE :: FMU)  . ((( (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) ))) \<longrightarrow> (\<comment>\<open>Transform a VDM `=` expression into an `eq_FMU` call\<close>
	(eq_FMU dummy0RANGE   (fst ((res fmu)))) \<and> (True::\<bool>))))) then
		(dummy0RANGE)
		else
		(undefined)))))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U (
		if ((\<exists> (dummy0RANGE :: FMU)  . ((( (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) ))) \<longrightarrow> (\<comment>\<open>Transform a VDM `=` expression into an `eq_FMU` call\<close>
	(eq_FMU dummy0RANGE   (fst ((res fmu)))) \<and> (True::\<bool>))))) then
		(dummy0RANGE)
		else
		(undefined))))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U (
		if ((\<exists> (dummy0RANGE :: FMU)  . ((( (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) ))) \<longrightarrow> (\<comment>\<open>Transform a VDM `=` expression into an `eq_FMU` call\<close>
	(eq_FMU dummy0RANGE   (fst ((res fmu)))) \<and> (True::\<bool>))))) then
		(dummy0RANGE)
		else
		(undefined)))))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U (
		if ((\<exists> (dummy0RANGE :: FMU)  . ((( (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) ))) \<longrightarrow> (\<comment>\<open>Transform a VDM `=` expression into an `eq_FMU` call\<close>
	(eq_FMU dummy0RANGE   (fst ((res fmu)))) \<and> (True::\<bool>))))) then
		(dummy0RANGE)
		else
		(undefined))))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U (
		if ((\<exists> (dummy0RANGE :: FMU)  . ((( (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) ))) \<longrightarrow> (\<comment>\<open>Transform a VDM `=` expression into an `eq_FMU` call\<close>
	(eq_FMU dummy0RANGE   (fst ((res fmu)))) \<and> (True::\<bool>))))) then
		(dummy0RANGE)
		else
		(undefined))))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U (
		if ((\<exists> (dummy0RANGE :: FMU)  . ((( (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) ))) \<longrightarrow> (\<comment>\<open>Transform a VDM `=` expression into an `eq_FMU` call\<close>
	(eq_FMU dummy0RANGE   (fst ((res fmu)))) \<and> (True::\<bool>))))) then
		(dummy0RANGE)
		else
		(undefined))))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U (
		if ((\<exists> (dummy0RANGE :: FMU)  . ((( (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) ))) \<longrightarrow> (\<comment>\<open>Transform a VDM `=` expression into an `eq_FMU` call\<close>
	(eq_FMU dummy0RANGE   (fst ((res fmu)))) \<and> (True::\<bool>))))) then
		(dummy0RANGE)
		else
		(undefined)))))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U (
		if ((\<exists> (dummy0RANGE :: FMU)  . ((( (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) ))) \<longrightarrow> (\<comment>\<open>Transform a VDM `=` expression into an `eq_FMU` call\<close>
	(eq_FMU dummy0RANGE   (fst ((res fmu)))) \<and> (True::\<bool>))))) then
		(dummy0RANGE)
		else
		(undefined))))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U (
		if ((\<exists> (dummy0RANGE :: FMU)  . ((( (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) ))) \<longrightarrow> (\<comment>\<open>Transform a VDM `=` expression into an `eq_FMU` call\<close>
	(eq_FMU dummy0RANGE   (fst ((res fmu)))) \<and> (True::\<bool>))))) then
		(dummy0RANGE)
		else
		(undefined)))))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U (
		if ((\<exists> (dummy0RANGE :: FMU)  . ((( (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) ))) \<longrightarrow> (\<comment>\<open>Transform a VDM `=` expression into an `eq_FMU` call\<close>
	(eq_FMU dummy0RANGE   (fst ((res fmu)))) \<and> (True::\<bool>))))) then
		(dummy0RANGE)
		else
		(undefined)))))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U (
		if ((\<exists> (dummy0RANGE :: FMU)  . ((( (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) ))) \<longrightarrow> (\<comment>\<open>Transform a VDM `=` expression into an `eq_FMU` call\<close>
	(eq_FMU dummy0RANGE   (fst ((res fmu)))) \<and> (True::\<bool>))))) then
		(dummy0RANGE)
		else
		(undefined))))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U (
		if ((\<exists> (dummy0RANGE :: FMU)  . ((( (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) ))) \<longrightarrow> (\<comment>\<open>Transform a VDM `=` expression into an `eq_FMU` call\<close>
	(eq_FMU dummy0RANGE   (fst ((res fmu)))) \<and> (True::\<bool>))))) then
		(dummy0RANGE)
		else
		(undefined))))) ) then
			(
		if ((\<exists> (dummy0RANGE :: FMU)  . ((( (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) ))) \<longrightarrow> (\<comment>\<open>Transform a VDM `=` expression into an `eq_FMU` call\<close>
	(eq_FMU dummy0RANGE   (fst ((res fmu)))) \<and> (True::\<bool>))))) then
		(dummy0RANGE)
		else
		(undefined))
		 else
			undefined
		)
		) 
		(truecnst )))
		;
		
(eventFMUs::Name VDMSet) = { fmu .   ((fmu \<in>(dom res)))  \<and> ((snd ((res fmu))) = (True::\<bool>)) }
		in
			(if (inv_Scenario M)
	 \<and> 
	((inv_Map ((inv_VDMSeq1' (inv_VDMChar))) 
		( (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U ))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U )))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U ))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U )))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U ))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U ))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U ))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U )))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U ))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U )))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U )))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U ))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U ))) )\<and>
		 (inv_bool )
		) res))
	 \<and> 
	((inv_Map ((inv_VDMSeq1' (inv_VDMChar))) inv_FMU  fmuMap))
	 \<and> 
	((inv_VDMSet' ((inv_VDMSeq1' (inv_VDMChar))) eventFMUs)) then
			(I)\<lparr>scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r := ((scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I))\<lparr>fmus\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r := fmuMap\<rparr>, fmusWithEvent\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r := eventFMUs, activeClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r := {}, inactiveClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r := ((inactiveClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I) \<union> (activeClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)), activeEquations\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r := {}, readyClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r := ((inactiveClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I) \<union> (activeClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)), readyEquations\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r := (((readyEquations\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I) \<union> (calculatedEquations\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) \<union> (activeEquations\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)), calculatedEquations\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r := {}, activeEquations\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r := {}\<rparr>
		 else
			undefined
		)
		)"

	
	
\<comment>\<open>VDM source: eventIteration: (Importer * set of (Name) -> Importer)
	eventIteration(I, relevantFMUs) ==
let I1:Importer = solveSystemOfEquations(I), I2:Importer = updateDiscreteState(I1, relevantFMUs) in I2
	pre (pre_solveSystemOfEquations(I) and (pre_updateDiscreteState(solveSystemOfEquations(I), relevantFMUs) and let fmus:set of (FMU) = (rng (relevantFMUs <: ((I.scenario).fmus))) in (pre_fmusSynchronized(fmus) and (fmusSynchronized(fmus) and (pre_assertFMUMode(fmus, {<EVENT>}) and assertFMUMode(fmus, {<EVENT>}))))))
	post let newfmus:set of (FMU) = (rng (relevantFMUs <: ((RESULT.scenario).fmus))), oldfmus:set of (FMU) = (rng (relevantFMUs <: ((I.scenario).fmus))) in (pre_eventSolved(RESULT, newfmus, oldfmus) and eventSolved(RESULT, newfmus, oldfmus))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1499:1\<close>

\<comment>\<open>VDM source: pre_eventIteration: (Importer * set of (Name) +> bool)
	pre_eventIteration(I, relevantFMUs) ==
(pre_solveSystemOfEquations(I) and (pre_updateDiscreteState(solveSystemOfEquations(I), relevantFMUs) and let fmus:set of (FMU) = (rng (relevantFMUs <: ((I.scenario).fmus))) in (pre_fmusSynchronized(fmus) and (fmusSynchronized(fmus) and (pre_assertFMUMode(fmus, {<EVENT>}) and assertFMUMode(fmus, {<EVENT>}))))))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1528:9\<close>
definition
	pre_eventIteration :: "Importer \<Rightarrow> Name VDMSet \<Rightarrow> bool"
where
	"pre_eventIteration I   relevantFMUs \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `pre_eventIteration` specification.\<close>
		(inv_Importer I  \<and>  (inv_VDMSet' (inv_Name) relevantFMUs))  \<and> 
		\<comment>\<open>User defined body of pre_eventIteration.\<close>
		((pre_solveSystemOfEquations I) \<and> ((pre_updateDiscreteState (solveSystemOfEquations I)   relevantFMUs) \<and> (
		let 
(fmus::FMU VDMSet) = (rng (relevantFMUs \<triangleleft> (fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I))))
		in
			(if ((inv_VDMSet' inv_FMU  fmus)) then
			((pre_fmusSynchronized fmus) \<and> ((fmusSynchronized fmus) \<and> ((pre_assertFMUMode fmus   {FMUMode.U_EVENT }) \<and> (assertFMUMode fmus   {FMUMode.U_EVENT }))))
		 else
			undefined
		)
		)))"


\<comment>\<open>VDM source: post_eventIteration: (Importer * set of (Name) * Importer +> bool)
	post_eventIteration(I, relevantFMUs, RESULT) ==
let newfmus:set of (FMU) = (rng (relevantFMUs <: ((RESULT.scenario).fmus))), oldfmus:set of (FMU) = (rng (relevantFMUs <: ((I.scenario).fmus))) in (pre_eventSolved(RESULT, newfmus, oldfmus) and eventSolved(RESULT, newfmus, oldfmus))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1536:9\<close>
definition
	post_eventIteration :: "Importer \<Rightarrow> Name VDMSet \<Rightarrow> Importer \<Rightarrow> bool"
where
	"post_eventIteration I   relevantFMUs   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `post_eventIteration` specification.\<close>
		(inv_Importer I  \<and>  (inv_VDMSet' (inv_Name) relevantFMUs)  \<and>  inv_Importer RESULT)  \<and> 
		\<comment>\<open>User defined body of post_eventIteration.\<close>
		(
		let 
(newfmus::FMU VDMSet) = (rng (relevantFMUs \<triangleleft> (fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r RESULT))))
		;
		
(oldfmus::FMU VDMSet) = (rng (relevantFMUs \<triangleleft> (fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I))))
		in
			(if ((inv_VDMSet' inv_FMU  newfmus))
	 \<and> 
	((inv_VDMSet' inv_FMU  oldfmus)) then
			((pre_eventSolved RESULT   newfmus   oldfmus) \<and> (eventSolved RESULT   newfmus   oldfmus))
		 else
			undefined
		)
		)"

definition
	eventIteration :: "Importer \<Rightarrow> Name VDMSet \<Rightarrow> Importer"
where
	"eventIteration I   relevantFMUs \<equiv> 
	\<comment>\<open>User defined body of eventIteration.\<close>
	(
		let 
(I1::Importer) = (solveSystemOfEquations I)
		;
		
(I2::Importer) = (updateDiscreteState I1   relevantFMUs)
		in
			(if (inv_Importer I1)
	 \<and> 
	(inv_Importer I2) then
			I2
		 else
			undefined
		)
		)"

	
	
\<comment>\<open>VDM source: createSchedule: (Importer -> Importer)
	createSchedule(I) ==
let timedBasedClocks:set of (TimeBasedClock) = ((I.scenario).timeBasedClocks) in mu(I, schedule |-> {(c.name) |-> ((c.period) + (c.shift)) | c in set timedBasedClocks})
	pre let fmus:set1 of (FMU) = (rng ((I.scenario).fmus)) in (pre_assertFMUMode(fmus, {<INIT>}) and (assertFMUMode(fmus, {<INIT>}) and (pre_fmusSynchronized(fmus) and (fmusSynchronized(fmus) and (pre_variablesSynchronized((I.scenario), {<discrete>, <continous>}) and variablesSynchronized((I.scenario), {<discrete>, <continous>}))))))
	post let fmus:set1 of (FMU) = (rng ((RESULT.scenario).fmus)) in (((dom (RESULT.schedule)) = {(c.name) | c in set ((RESULT.scenario).timeBasedClocks)}) and (pre_assertFMUMode(fmus, {<INIT>}) and (assertFMUMode(fmus, {<INIT>}) and (pre_fmusSynchronized(fmus) and (fmusSynchronized(fmus) and (pre_ImporterNotAffected(I, RESULT) and (ImporterNotAffected(I, RESULT) and (pre_variablesSynchronized((RESULT.scenario), {<discrete>, <continous>}) and variablesSynchronized((RESULT.scenario), {<discrete>, <continous>})))))))))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1546:5\<close>

\<comment>\<open>VDM source: pre_createSchedule: (Importer +> bool)
	pre_createSchedule(I) ==
let fmus:set1 of (FMU) = (rng ((I.scenario).fmus)) in (pre_assertFMUMode(fmus, {<INIT>}) and (assertFMUMode(fmus, {<INIT>}) and (pre_fmusSynchronized(fmus) and (fmusSynchronized(fmus) and (pre_variablesSynchronized((I.scenario), {<discrete>, <continous>}) and variablesSynchronized((I.scenario), {<discrete>, <continous>}))))))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1553:9\<close>
definition
	pre_createSchedule :: "Importer \<Rightarrow> bool"
where
	"pre_createSchedule I \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `pre_createSchedule` specification.\<close>
		(inv_Importer I)  \<and> 
		\<comment>\<open>User defined body of pre_createSchedule.\<close>
		(
		let 
(fmus::FMU VDMSet1) = (rng (fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)))
		in
			(if ((inv_VDMSet1' inv_FMU  fmus)) then
			((pre_assertFMUMode fmus   {FMUMode.U_INIT }) \<and> ((assertFMUMode fmus   {FMUMode.U_INIT }) \<and> ((pre_fmusSynchronized fmus) \<and> ((fmusSynchronized fmus) \<and> ((pre_variablesSynchronized (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)   {PortType.U_discrete  , PortType.U_continous }) \<and> (variablesSynchronized (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)   {PortType.U_discrete  , PortType.U_continous }))))))
		 else
			undefined
		)
		)"


\<comment>\<open>VDM source: post_createSchedule: (Importer * Importer +> bool)
	post_createSchedule(I, RESULT) ==
let fmus:set1 of (FMU) = (rng ((RESULT.scenario).fmus)) in (((dom (RESULT.schedule)) = {(c.name) | c in set ((RESULT.scenario).timeBasedClocks)}) and (pre_assertFMUMode(fmus, {<INIT>}) and (assertFMUMode(fmus, {<INIT>}) and (pre_fmusSynchronized(fmus) and (fmusSynchronized(fmus) and (pre_ImporterNotAffected(I, RESULT) and (ImporterNotAffected(I, RESULT) and (pre_variablesSynchronized((RESULT.scenario), {<discrete>, <continous>}) and variablesSynchronized((RESULT.scenario), {<discrete>, <continous>})))))))))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1561:9\<close>
definition
	post_createSchedule :: "Importer \<Rightarrow> Importer \<Rightarrow> bool"
where
	"post_createSchedule I   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `post_createSchedule` specification.\<close>
		(inv_Importer I  \<and>  inv_Importer RESULT)  \<and> 
		\<comment>\<open>User defined body of post_createSchedule.\<close>
		(
		let 
(fmus::FMU VDMSet1) = (rng (fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r RESULT)))
		in
			(if ((inv_VDMSet1' inv_FMU  fmus)) then
			(((dom (schedule\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r RESULT)) = { (name\<^sub>T\<^sub>i\<^sub>m\<^sub>e\<^sub>B\<^sub>a\<^sub>s\<^sub>e\<^sub>d\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k c) | c .  ((c \<in>(timeBasedClocks\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r RESULT))))  }) \<and> ((pre_assertFMUMode fmus   {FMUMode.U_INIT }) \<and> ((assertFMUMode fmus   {FMUMode.U_INIT }) \<and> ((pre_fmusSynchronized fmus) \<and> ((fmusSynchronized fmus) \<and> ((pre_ImporterNotAffected I   RESULT) \<and> ((ImporterNotAffected I   RESULT) \<and> ((pre_variablesSynchronized (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r RESULT)   {PortType.U_discrete  , PortType.U_continous }) \<and> (variablesSynchronized (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r RESULT)   {PortType.U_discrete  , PortType.U_continous })))))))))
		 else
			undefined
		)
		)"

definition
	createSchedule :: "Importer \<Rightarrow> Importer"
where
	"createSchedule I \<equiv> 
	\<comment>\<open>User defined body of createSchedule.\<close>
	(
		let 
(timedBasedClocks::TimeBasedClock VDMSet) = (timeBasedClocks\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I))
		in
			(if ((inv_VDMSet' inv_TimeBasedClock  timedBasedClocks)) then
			(I)\<lparr>schedule\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r := (\<comment>\<open>VDM Map comprehension is translated as a lambda-term through mapCompSetBound\<close>
		mapCompSetBound 
		{(name\<^sub>T\<^sub>i\<^sub>m\<^sub>e\<^sub>B\<^sub>a\<^sub>s\<^sub>e\<^sub>d\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k c)} 
		{((period\<^sub>T\<^sub>i\<^sub>m\<^sub>e\<^sub>B\<^sub>a\<^sub>s\<^sub>e\<^sub>d\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k c) + (shift\<^sub>T\<^sub>i\<^sub>m\<^sub>e\<^sub>B\<^sub>a\<^sub>s\<^sub>e\<^sub>d\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k c))} 
		((inv_VDMSeq1' (inv_VDMChar))) 
		(inv_VDMReal) 
		(
	\<lambda> (dummy0DOMAIN :: Name)   (dummy0RANGE :: VDMReal) .
		(if ((((inv_VDMSeq1' (inv_VDMChar) dummy0DOMAIN))))  \<and>  (((inv_VDMReal dummy0RANGE))) \<and> ((inv_VDMSeq1' (inv_VDMChar) (
		if ((\<exists> (dummy0DOMAIN :: Name)  . (((((inv_VDMSeq1' (inv_VDMChar) dummy0DOMAIN)))) \<longrightarrow> ((dummy0DOMAIN = (name\<^sub>T\<^sub>i\<^sub>m\<^sub>e\<^sub>B\<^sub>a\<^sub>s\<^sub>e\<^sub>d\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k c)) \<and> (True::\<bool>))))) then
		(dummy0DOMAIN)
		else
		(undefined)))) then
			(
		if ((\<exists> (dummy0DOMAIN :: Name)  . (((((inv_VDMSeq1' (inv_VDMChar) dummy0DOMAIN)))) \<longrightarrow> ((dummy0DOMAIN = (name\<^sub>T\<^sub>i\<^sub>m\<^sub>e\<^sub>B\<^sub>a\<^sub>s\<^sub>e\<^sub>d\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k c)) \<and> (True::\<bool>))))) then
		(dummy0DOMAIN)
		else
		(undefined))
		 else
			undefined
		)
		) 
		(
	\<lambda> (dummy0DOMAIN :: Name)   (dummy0RANGE :: VDMReal) .
		(if ((((inv_VDMSeq1' (inv_VDMChar) dummy0DOMAIN))))  \<and>  (((inv_VDMReal dummy0RANGE))) \<and> (inv_VDMReal (
		if ((\<exists> (dummy0RANGE :: VDMReal)  . ((((inv_VDMReal dummy0RANGE))) \<longrightarrow> ((dummy0RANGE = ((period\<^sub>T\<^sub>i\<^sub>m\<^sub>e\<^sub>B\<^sub>a\<^sub>s\<^sub>e\<^sub>d\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k c) + (shift\<^sub>T\<^sub>i\<^sub>m\<^sub>e\<^sub>B\<^sub>a\<^sub>s\<^sub>e\<^sub>d\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k c))) \<and> (True::\<bool>))))) then
		(dummy0RANGE)
		else
		(undefined))) then
			(
		if ((\<exists> (dummy0RANGE :: VDMReal)  . ((((inv_VDMReal dummy0RANGE))) \<longrightarrow> ((dummy0RANGE = ((period\<^sub>T\<^sub>i\<^sub>m\<^sub>e\<^sub>B\<^sub>a\<^sub>s\<^sub>e\<^sub>d\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k c) + (shift\<^sub>T\<^sub>i\<^sub>m\<^sub>e\<^sub>B\<^sub>a\<^sub>s\<^sub>e\<^sub>d\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k c))) \<and> (True::\<bool>))))) then
		(dummy0RANGE)
		else
		(undefined))
		 else
			undefined
		)
		) 
		(truecnst ))\<rparr>
		 else
			undefined
		)
		)"

	
	
\<comment>\<open>VDM source: calculateSchedule: (FMU * set of (Ref) -> map (FMURef) to (Real1))
	calculateSchedule(fmu, clocks) ==
{mk_FMURef((fmu.name), clock) |-> next_tm(fmu, clock) | clock in set clocks}
	pre ((forall clock in set clocks & pre_next_tm(fmu, clock)) and (clocks subset {(c.ref) | c in set (fmu.clocks) & (((c.type) = <input>) and ((c.interval) <> <triggered>))}))
	post ((card (dom RESULT)) = (card clocks))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1573:5\<close>

\<comment>\<open>VDM source: pre_calculateSchedule: (FMU * set of (Ref) +> bool)
	pre_calculateSchedule(fmu, clocks) ==
((forall clock in set clocks & pre_next_tm(fmu, clock)) and (clocks subset {(c.ref) | c in set (fmu.clocks) & (((c.type) = <input>) and ((c.interval) <> <triggered>))}))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1578:9\<close>
definition
	pre_calculateSchedule :: "FMU \<Rightarrow> Ref VDMSet \<Rightarrow> bool"
where
	"pre_calculateSchedule fmu   clocks \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `pre_calculateSchedule` specification.\<close>
		(inv_FMU fmu  \<and>  (inv_VDMSet' (inv_Ref) clocks))  \<and> 
		\<comment>\<open>User defined body of pre_calculateSchedule.\<close>
		((\<forall> clock \<in> clocks  . (pre_next_tm fmu   clock)) \<and> (clocks \<subseteq> { (ref\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k c) | c .  ((c \<in>(clocks\<^sub>F\<^sub>M\<^sub>U fmu)))  \<and> (((type\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k c) = Causality.U_input ) \<and> ((interval\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k c) \<noteq> Interval.U_triggered )) }))"


\<comment>\<open>VDM source: post_calculateSchedule: (FMU * set of (Ref) * map (FMURef) to (Real1) +> bool)
	post_calculateSchedule(fmu, clocks, RESULT) ==
((card (dom RESULT)) = (card clocks))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1579:26\<close>
definition
	post_calculateSchedule :: "FMU \<Rightarrow> Ref VDMSet \<Rightarrow> (FMURef \<rightharpoonup> Real1) \<Rightarrow> bool"
where
	"post_calculateSchedule fmu   clocks   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `post_calculateSchedule` specification.\<close>
		(inv_FMU fmu  \<and>  (inv_VDMSet' (inv_Ref) clocks)  \<and>  (inv_Map inv_FMURef  (inv_Real1) RESULT))  \<and> 
		\<comment>\<open>User defined body of post_calculateSchedule.\<close>
		((vdm_card (dom RESULT)) = (vdm_card clocks))"

definition
	calculateSchedule :: "FMU \<Rightarrow> Ref VDMSet \<Rightarrow> (FMURef \<rightharpoonup> Real1)"
where
	"calculateSchedule fmu   clocks \<equiv> 
	\<comment>\<open>User defined body of calculateSchedule.\<close>
	(\<comment>\<open>VDM Map comprehension is translated as a lambda-term through mapCompSetBound\<close>
		mapCompSetBound 
		{\<lparr>name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f = (name\<^sub>F\<^sub>M\<^sub>U fmu), ref\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f = clock\<rparr>} 
		{ (next_tm fmu   clock) | clock .  ((clock \<in>clocks))  } 
		
		 ((((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f FMURef)))) \<and> 
		 (((inv_VDMNat (ref\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f FMURef))))
		 ) 
		((inv_RealNaN )) 
		(
	\<lambda> (dummy0DOMAIN :: FMURef)   (dummy0RANGE :: RealNaN) .
		(if ((
		 ((((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f dummy0DOMAIN)))) \<and> 
		 (((inv_VDMNat (ref\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f dummy0DOMAIN))))
		 )))  \<and>  ((((case dummy0RANGE of
		 RealNaN.U_NaN  \<Rightarrow> (inv_True dummy0RANGE)
		  | RealNaN.U_VDMReal dummy0RANGE \<Rightarrow> (inv_VDMReal dummy0RANGE)
		 )))) \<and>  ((((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f (
		if ((\<exists> (dummy0DOMAIN :: FMURef)  . (((
		 ((((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f dummy0DOMAIN)))) \<and> 
		 (((inv_VDMNat (ref\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f dummy0DOMAIN))))
		 ))) \<longrightarrow> (\<comment>\<open>Transform a VDM `=` expression into an `eq_FMURef` call\<close>
	(eq_FMURef dummy0DOMAIN   \<lparr>name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f = (name\<^sub>F\<^sub>M\<^sub>U fmu), ref\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f = clock\<rparr>) \<and> (True::\<bool>))))) then
		(dummy0DOMAIN)
		else
		(undefined)))))) \<and> 
		 (((inv_VDMNat (ref\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f (
		if ((\<exists> (dummy0DOMAIN :: FMURef)  . (((
		 ((((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f dummy0DOMAIN)))) \<and> 
		 (((inv_VDMNat (ref\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f dummy0DOMAIN))))
		 ))) \<longrightarrow> (\<comment>\<open>Transform a VDM `=` expression into an `eq_FMURef` call\<close>
	(eq_FMURef dummy0DOMAIN   \<lparr>name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f = (name\<^sub>F\<^sub>M\<^sub>U fmu), ref\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f = clock\<rparr>) \<and> (True::\<bool>))))) then
		(dummy0DOMAIN)
		else
		(undefined)))))) ) then
			(
		if ((\<exists> (dummy0DOMAIN :: FMURef)  . ((( ((((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f dummy0DOMAIN)))) \<and> 
		 (((inv_VDMNat (ref\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f dummy0DOMAIN)))) ))) \<longrightarrow> (\<comment>\<open>Transform a VDM `=` expression into an `eq_FMURef` call\<close>
	(eq_FMURef dummy0DOMAIN   \<lparr>name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f = (name\<^sub>F\<^sub>M\<^sub>U fmu), ref\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f = clock\<rparr>) \<and> (True::\<bool>))))) then
		(dummy0DOMAIN)
		else
		(undefined))
		 else
			undefined
		)
		) 
		(
	\<lambda> (dummy0DOMAIN :: FMURef)   (dummy0RANGE :: RealNaN) .
		(if (( ((((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f dummy0DOMAIN)))) \<and> 
		 (((inv_VDMNat (ref\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f dummy0DOMAIN)))) )))  \<and>  ((((case dummy0RANGE of
		 RealNaN.U_NaN  \<Rightarrow> (inv_True dummy0RANGE)
		  | RealNaN.U_VDMReal dummy0RANGE \<Rightarrow> (inv_VDMReal dummy0RANGE)
		 )))) \<and> ((case (
		if ((\<exists> clock \<in> clocks  . ((clock \<in> clocks) \<and> ((dummy0RANGE = (next_tm fmu   clock)) \<and> (True::\<bool>))))) then
		(dummy0RANGE)
		else
		(undefined)) of
		 RealNaN.U_NaN  \<Rightarrow> (inv_True (
		if ((\<exists> clock \<in> clocks  . ((clock \<in> clocks) \<and> ((dummy0RANGE = (next_tm fmu   clock)) \<and> (True::\<bool>))))) then
		(dummy0RANGE)
		else
		(undefined)))
		  | RealNaN.U_VDMReal (
		if ((\<exists> clock \<in> clocks  . ((clock \<in> clocks) \<and> ((dummy0RANGE = (next_tm fmu   clock)) \<and> (True::\<bool>))))) then
		(dummy0RANGE)
		else
		(undefined)) \<Rightarrow> (inv_VDMReal (
		if ((\<exists> clock \<in> clocks  . ((clock \<in> clocks) \<and> ((dummy0RANGE = (next_tm fmu   clock)) \<and> (True::\<bool>))))) then
		(dummy0RANGE)
		else
		(undefined)))
		 )) then
			(
		if ((\<exists> clock \<in> clocks  . ((clock \<in> clocks) \<and> ((dummy0RANGE = (next_tm fmu   clock)) \<and> (True::\<bool>))))) then
		(dummy0RANGE)
		else
		(undefined))
		 else
			undefined
		)
		) 
		(truecnst ))"

	
	
\<comment>\<open>VDM source: clockedSimulationAlgorithm: (Importer * set of (FMURef) -> Importer)
	clockedSimulationAlgorithm(I, activeClocks) ==
let eventFMUs:set1 of (Name) = ((I.fmusWithEvent) union {(clock.name) | clock in set activeClocks}), relevantFMUs:set of (Name) = calculateRelevantFMUs((I.scenario), eventFMUs, ((dom ((I.scenario).fmus)) \ eventFMUs)), I1:Importer = enterEventMode(I, relevantFMUs), I2:Importer = activateClocks(I1, [clock | clock in set activeClocks]), I3:Importer = eventIteration(I2, relevantFMUs) in (if ((I3.fmusWithEvent) = {})
then enterStepMode(I3, relevantFMUs)
else clockedSimulationAlgorithm(I, activeClocks))
	pre (pre_preEventMode(I, activeClocks) and (preEventMode(I, activeClocks) and let eventFMUs:set1 of (Name) = ((I.fmusWithEvent) union {(clock.name) | clock in set activeClocks}), notAddedFMUS:set of (Name) = ((dom ((I.scenario).fmus)) \ eventFMUs) in (pre_calculateRelevantFMUs((I.scenario), eventFMUs, notAddedFMUS) and let relevantFMUs:set of (Name) = calculateRelevantFMUs((I.scenario), eventFMUs, notAddedFMUS) in (pre_enterEventMode(I, relevantFMUs) and let I1:Importer = enterEventMode(I, relevantFMUs) in (pre_activateClocks(I1, [clock | clock in set activeClocks]) and let I2:Importer = activateClocks(I1, [clock | clock in set activeClocks]) in (pre_eventIteration(I2, relevantFMUs) and let I3:Importer = eventIteration(I2, relevantFMUs) in (((I3.fmusWithEvent) <> {}) => ((pre_clockedSimulationAlgorithm(I3, activeClocks) and ((I3.fmusWithEvent) = {})) => pre_enterStepMode(I3, relevantFMUs)))))))))
	post (pre_postEventMode(RESULT) and postEventMode(RESULT))
	measure not yet specified\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1602:5\<close>

\<comment>\<open>VDM source: pre_clockedSimulationAlgorithm: (Importer * set of (FMURef) +> bool)
	pre_clockedSimulationAlgorithm(I, activeClocks) ==
(pre_preEventMode(I, activeClocks) and (preEventMode(I, activeClocks) and let eventFMUs:set1 of (Name) = ((I.fmusWithEvent) union {(clock.name) | clock in set activeClocks}), notAddedFMUS:set of (Name) = ((dom ((I.scenario).fmus)) \ eventFMUs) in (pre_calculateRelevantFMUs((I.scenario), eventFMUs, notAddedFMUS) and let relevantFMUs:set of (Name) = calculateRelevantFMUs((I.scenario), eventFMUs, notAddedFMUS) in (pre_enterEventMode(I, relevantFMUs) and let I1:Importer = enterEventMode(I, relevantFMUs) in (pre_activateClocks(I1, [clock | clock in set activeClocks]) and let I2:Importer = activateClocks(I1, [clock | clock in set activeClocks]) in (pre_eventIteration(I2, relevantFMUs) and let I3:Importer = eventIteration(I2, relevantFMUs) in (((I3.fmusWithEvent) <> {}) => ((pre_clockedSimulationAlgorithm(I3, activeClocks) and ((I3.fmusWithEvent) = {})) => pre_enterStepMode(I3, relevantFMUs)))))))))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1637:9\<close>
definition
	pre_clockedSimulationAlgorithm :: "Importer \<Rightarrow> FMURef VDMSet \<Rightarrow> bool"
where
	"pre_clockedSimulationAlgorithm I   activeClocks \<equiv> 
	\<comment>\<open>Implicitly defined type invariant checks for  `pre_clockedSimulationAlgorithm` specification.\<close>
	(inv_Importer I  \<and>  (inv_VDMSet' inv_FMURef  activeClocks))  \<and> 
	\<comment>\<open>User defined body of pre_clockedSimulationAlgorithm.\<close>
	((pre_preEventMode I   activeClocks) \<and> ((preEventMode I   activeClocks) \<and> (
		let 
(eventFMUs::Name VDMSet1) = ((fmusWithEvent\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I) \<union> { (name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f clock) | clock .  ((clock \<in>activeClocks))  })
		;
		
(notAddedFMUS::Name VDMSet) = ((dom (fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I))) - eventFMUs)
		in
			(if ((inv_VDMSet1' ((inv_VDMSeq1' (inv_VDMChar))) eventFMUs))
	 \<and> 
	((inv_VDMSet' ((inv_VDMSeq1' (inv_VDMChar))) notAddedFMUS)) then
			((pre_calculateRelevantFMUs (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)   eventFMUs   notAddedFMUS) \<and> (
		let 
(relevantFMUs::Name VDMSet) = (calculateRelevantFMUs (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)   eventFMUs   notAddedFMUS)
		in
			(if ((inv_VDMSet' ((inv_VDMSeq1' (inv_VDMChar))) relevantFMUs)) then
			((pre_enterEventMode I   relevantFMUs) \<and> (
		let 
(I1::Importer) = (enterEventMode I   relevantFMUs)
		in
			(if (inv_Importer I1) then
			((pre_activateClocks I1   [ clock . clock \<leftarrow> sorted_list_of_set (activeClocks) , ((clock \<in>activeClocks)) ]
	\<comment>\<open>`Set bind `(clock \<in> activeClocks)` in sequence comprehension requires its Isabelle type to instantiate class linorder.`   This can be a problem if the target type of @{term \<open>activeClocks\<close>}   has a VDM ord_ predicate.\<close> ) \<and> (
		let 
(I2::Importer) = (activateClocks I1   [ clock . clock \<leftarrow> sorted_list_of_set (activeClocks) , ((clock \<in>activeClocks)) ]
	\<comment>\<open>`Set bind `(clock \<in> activeClocks)` in sequence comprehension requires its Isabelle type to instantiate class linorder.`   This can be a problem if the target type of @{term \<open>activeClocks\<close>}   has a VDM ord_ predicate.\<close> )
		in
			(if (inv_Importer I2) then
			((pre_eventIteration I2   relevantFMUs) \<and> (
		let 
(I3::Importer) = (eventIteration I2   relevantFMUs)
		in
			(if (inv_Importer I3) then
			(((fmusWithEvent\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I3) \<noteq> {}) \<longrightarrow> (((pre_clockedSimulationAlgorithm I3   activeClocks) \<and> ((fmusWithEvent\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I3) = {})) \<longrightarrow> (pre_enterStepMode I3   relevantFMUs)))
		 else
			undefined
		)
		))
		 else
			undefined
		)
		))
		 else
			undefined
		)
		))
		 else
			undefined
		)
		))
		 else
			undefined
		)
		)))"


\<comment>\<open>VDM source: post_clockedSimulationAlgorithm: (Importer * set of (FMURef) * Importer +> bool)
	post_clockedSimulationAlgorithm(I, activeClocks, RESULT) ==
(pre_postEventMode(RESULT) and postEventMode(RESULT))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1661:9\<close>
definition
	post_clockedSimulationAlgorithm :: "Importer \<Rightarrow> FMURef VDMSet \<Rightarrow> Importer \<Rightarrow> bool"
where
	"post_clockedSimulationAlgorithm I   activeClocks   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `post_clockedSimulationAlgorithm` specification.\<close>
		(inv_Importer I  \<and>  (inv_VDMSet' inv_FMURef  activeClocks)  \<and>  inv_Importer RESULT)  \<and> 
		\<comment>\<open>User defined body of post_clockedSimulationAlgorithm.\<close>
		((pre_postEventMode RESULT) \<and> (postEventMode RESULT))"

fun
	clockedSimulationAlgorithm :: "Importer \<Rightarrow> FMURef VDMSet \<Rightarrow> Importer"
where
	"clockedSimulationAlgorithm I   activeClocks = 
	\<comment>\<open>User defined body of clockedSimulationAlgorithm.\<close>
	(
		let 
(eventFMUs::Name VDMSet1) = ((fmusWithEvent\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I) \<union> { (name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f clock) | clock .  ((clock \<in>activeClocks))  })
		;
		
(relevantFMUs::Name VDMSet) = (calculateRelevantFMUs (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)   eventFMUs   ((dom (fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I))) - eventFMUs))
		;
		
(I1::Importer) = (enterEventMode I   relevantFMUs)
		;
		
(I2::Importer) = (activateClocks I1   [ clock . clock \<leftarrow> sorted_list_of_set (activeClocks) , ((clock \<in>activeClocks)) ]
	\<comment>\<open>`Set bind `(clock \<in> activeClocks)` in sequence comprehension requires its Isabelle type to instantiate class linorder.`   This can be a problem if the target type of @{term \<open>activeClocks\<close>}   has a VDM ord_ predicate.\<close> )
		;
		
(I3::Importer) = (eventIteration I2   relevantFMUs)
		in
			(if ((inv_VDMSet1' ((inv_VDMSeq1' (inv_VDMChar))) eventFMUs))
	 \<and> 
	((inv_VDMSet' ((inv_VDMSeq1' (inv_VDMChar))) relevantFMUs))
	 \<and> 
	(inv_Importer I1)
	 \<and> 
	(inv_Importer I2)
	 \<and> 
	(inv_Importer I3) then
			(
		if (((fmusWithEvent\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I3) = {})) then
		((enterStepMode I3   relevantFMUs))
		else
		((clockedSimulationAlgorithm I   activeClocks)))
		 else
			undefined
		)
		)"

	
	
\<comment>\<open>VDM source: minset: (set of (Real1) * Real1 -> Real1)
	minset(s, leomin) ==
(if (s = {})
then leomin
else let e in set s in let new_set:set of (Real1) = (s \ {e}) in (if (e < leomin)
then minset(new_set, e)
else minset(new_set, leomin)))
	pre ((s <> {}) => let e in set s in let new_set:set of (Real1) = (s \ {e}) in pre_minset(new_set, e))
	post (forall elem in set s & (elem >= RESULT))
	measure (card s)\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1667:5\<close>

\<comment>\<open>VDM source: pre_minset: (set of (Real1) * Real1 +> bool)
	pre_minset(s, leomin) ==
((s <> {}) => let e in set s in let new_set:set of (Real1) = (s \ {e}) in pre_minset(new_set, e))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1681:17\<close>
definition
	pre_minset :: "Real1 VDMSet \<Rightarrow> Real1 \<Rightarrow> bool"
where
	"pre_minset s   leomin \<equiv> 
	\<comment>\<open>Implicitly defined type invariant checks for  `pre_minset` specification.\<close>
	((inv_VDMSet' (inv_Real1) s)  \<and>  (inv_Real1 leomin))  \<and> 
	\<comment>\<open>User defined body of pre_minset.\<close>
	((s \<noteq> {}) \<longrightarrow> (
		SOME (dummy0::bool) .(dummy0 \<in> { (
		let 
(new_set::Real1 VDMSet) = (s - {e})
		in
			(if ((inv_VDMSet' ((inv_VDMReal)) new_set)) then
			(pre_minset new_set   e)
		 else
			undefined
		)
		) | e .  ((e \<in>s))  })))"


\<comment>\<open>VDM source: post_minset: (set of (Real1) * Real1 * Real1 +> bool)
	post_minset(s, leomin, RESULT) ==
(forall elem in set s & (elem >= RESULT))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1687:9\<close>
definition
	post_minset :: "Real1 VDMSet \<Rightarrow> Real1 \<Rightarrow> Real1 \<Rightarrow> bool"
where
	"post_minset s   leomin   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `post_minset` specification.\<close>
		((inv_VDMSet' (inv_Real1) s)  \<and>  (inv_Real1 leomin)  \<and>  (inv_Real1 RESULT))  \<and> 
		\<comment>\<open>User defined body of post_minset.\<close>
		(\<forall> elem \<in> s  . (elem \<ge> RESULT))"

fun
	minset :: "Real1 VDMSet \<Rightarrow> Real1 \<Rightarrow> Real1"
where
	"minset s   leomin = 
	\<comment>\<open>User defined body of minset.\<close>
	(
		if ((s = {})) then
		(leomin)
		else
		((
		SOME (dummy0::Real1) .(dummy0 \<in> { (
		let 
(new_set::Real1 VDMSet) = (s - {e})
		in
			(if ((inv_VDMSet' ((inv_VDMReal)) new_set)) then
			(
		if ((e < leomin)) then
		((minset new_set   e))
		else
		((minset new_set   leomin)))
		 else
			undefined
		)
		) | e .  ((e \<in>s))  }))))"

	
	
\<comment>\<open>VDM source: selectMinStep: (set1 of (Real1) -> Real1)
	selectMinStep(steps) ==
minset(steps, 10000)
	pre pre_minset(steps, 10000)
	post (forall elem in set steps & (elem >= RESULT))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1707:5\<close>

\<comment>\<open>VDM source: pre_selectMinStep: (set1 of (Real1) +> bool)
	pre_selectMinStep(steps) ==
pre_minset(steps, 10000)\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1709:9\<close>
definition
	pre_selectMinStep :: "Real1 VDMSet1 \<Rightarrow> bool"
where
	"pre_selectMinStep steps \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `pre_selectMinStep` specification.\<close>
		((inv_VDMSet1' (inv_Real1) steps))  \<and> 
		\<comment>\<open>User defined body of pre_selectMinStep.\<close>
		(pre_minset steps   (10000::VDMNat1))"


\<comment>\<open>VDM source: post_selectMinStep: (set1 of (Real1) * Real1 +> bool)
	post_selectMinStep(steps, RESULT) ==
(forall elem in set steps & (elem >= RESULT))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1710:10\<close>
definition
	post_selectMinStep :: "Real1 VDMSet1 \<Rightarrow> Real1 \<Rightarrow> bool"
where
	"post_selectMinStep steps   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `post_selectMinStep` specification.\<close>
		((inv_VDMSet1' (inv_Real1) steps)  \<and>  (inv_Real1 RESULT))  \<and> 
		\<comment>\<open>User defined body of post_selectMinStep.\<close>
		(\<forall> elem \<in> steps  . (elem \<ge> RESULT))"

definition
	selectMinStep :: "Real1 VDMSet1 \<Rightarrow> Real1"
where
	"selectMinStep steps \<equiv> 
	\<comment>\<open>User defined body of selectMinStep.\<close>
	(minset steps   (10000::VDMNat1))"

	
	
\<comment>\<open>VDM source: initialization: (Importer -> Importer)
	initialization(I) ==
let I1:Importer = initializeData(I) in let I2:Importer = createSchedule(I1) in enterStepMode(I2, (dom ((I2.scenario).fmus)))
	pre (pre_preInitialization(I) and (preInitialization(I) and (pre_initializeData(I) and let I1:Importer = initializeData(I) in (pre_createSchedule(I1) and let I2:Importer = createSchedule(I1) in pre_enterStepMode(I2, (dom ((I2.scenario).fmus)))))))
	post (pre_preCoSimulationStep((RESULT.scenario), (RESULT.time)) and (preCoSimulationStep((RESULT.scenario), (RESULT.time)) and (pre_ImporterNotAffected(RESULT, I) and (ImporterNotAffected(RESULT, I) and ((RESULT.time) = mk_Time(0, 0))))))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1716:5\<close>

\<comment>\<open>VDM source: pre_initialization: (Importer +> bool)
	pre_initialization(I) ==
(pre_preInitialization(I) and (preInitialization(I) and (pre_initializeData(I) and let I1:Importer = initializeData(I) in (pre_createSchedule(I1) and let I2:Importer = createSchedule(I1) in pre_enterStepMode(I2, (dom ((I2.scenario).fmus)))))))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1734:9\<close>
definition
	pre_initialization :: "Importer \<Rightarrow> bool"
where
	"pre_initialization I \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `pre_initialization` specification.\<close>
		(inv_Importer I)  \<and> 
		\<comment>\<open>User defined body of pre_initialization.\<close>
		((pre_preInitialization I) \<and> ((preInitialization I) \<and> ((pre_initializeData I) \<and> (
		let 
(I1::Importer) = (initializeData I)
		in
			(if (inv_Importer I1) then
			((pre_createSchedule I1) \<and> (
		let 
(I2::Importer) = (createSchedule I1)
		in
			(if (inv_Importer I2) then
			(pre_enterStepMode I2   (dom (fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I2))))
		 else
			undefined
		)
		))
		 else
			undefined
		)
		))))"


\<comment>\<open>VDM source: post_initialization: (Importer * Importer +> bool)
	post_initialization(I, RESULT) ==
(pre_preCoSimulationStep((RESULT.scenario), (RESULT.time)) and (preCoSimulationStep((RESULT.scenario), (RESULT.time)) and (pre_ImporterNotAffected(RESULT, I) and (ImporterNotAffected(RESULT, I) and ((RESULT.time) = mk_Time(0, 0))))))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1744:9\<close>
definition
	post_initialization :: "Importer \<Rightarrow> Importer \<Rightarrow> bool"
where
	"post_initialization I   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `post_initialization` specification.\<close>
		(inv_Importer I  \<and>  inv_Importer RESULT)  \<and> 
		\<comment>\<open>User defined body of post_initialization.\<close>
		((pre_preCoSimulationStep (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r RESULT)   (time\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r RESULT)) \<and> ((preCoSimulationStep (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r RESULT)   (time\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r RESULT)) \<and> ((pre_ImporterNotAffected RESULT   I) \<and> ((ImporterNotAffected RESULT   I) \<and> \<comment>\<open>Transform a VDM `=` expression into an `eq_Time` call\<close>
	(eq_Time (time\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r RESULT)   \<lparr>r\<^sub>T\<^sub>i\<^sub>m\<^sub>e = (0::VDMNat), i\<^sub>T\<^sub>i\<^sub>m\<^sub>e = (0::VDMNat)\<rparr>)))))"

definition
	initialization :: "Importer \<Rightarrow> Importer"
where
	"initialization I \<equiv> 
	\<comment>\<open>User defined body of initialization.\<close>
	(
		let 
(I1::Importer) = (initializeData I)
		in
			(if (inv_Importer I1) then
			(
		let 
(I2::Importer) = (createSchedule I1)
		in
			(if (inv_Importer I2) then
			(enterStepMode I2   (dom (fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I2))))
		 else
			undefined
		)
		)
		 else
			undefined
		)
		)"

	
	
\<comment>\<open>VDM source: postCosimulationStep: (Scenario * set1 of (FMU) -> bool)
	postCosimulationStep(scenario, oldFMUs) ==
let fmus:set1 of (FMU) = (rng (scenario.fmus)) in (assertFMUMode(fmus, {<STEP>}) and (variablesSynchronized(scenario, {<continous>}) and (fmusSynchronized(fmus) and timeAdvanced(fmus, oldFMUs, false))))
	pre (pre_variablesSynchronized(scenario, {<continous>}) and let fmus:set1 of (FMU) = (rng (scenario.fmus)) in (pre_assertFMUMode(fmus, {<STEP>}) and (pre_fmusSynchronized(fmus) and pre_timeAdvanced(fmus, oldFMUs, false))))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1750:5\<close>

\<comment>\<open>VDM source: pre_postCosimulationStep: (Scenario * set1 of (FMU) +> bool)
	pre_postCosimulationStep(scenario, oldFMUs) ==
(pre_variablesSynchronized(scenario, {<continous>}) and let fmus:set1 of (FMU) = (rng (scenario.fmus)) in (pre_assertFMUMode(fmus, {<STEP>}) and (pre_fmusSynchronized(fmus) and pre_timeAdvanced(fmus, oldFMUs, false))))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1759:9\<close>
definition
	pre_postCosimulationStep :: "Scenario \<Rightarrow> FMU VDMSet1 \<Rightarrow> bool"
where
	"pre_postCosimulationStep scenario   oldFMUs \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `pre_postCosimulationStep` specification.\<close>
		(inv_Scenario scenario  \<and>  (inv_VDMSet1' inv_FMU  oldFMUs))  \<and> 
		\<comment>\<open>User defined body of pre_postCosimulationStep.\<close>
		((pre_variablesSynchronized scenario   {PortType.U_continous }) \<and> (
		let 
(fmus::FMU VDMSet1) = (rng (fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o scenario))
		in
			(if ((inv_VDMSet1' inv_FMU  fmus)) then
			((pre_assertFMUMode fmus   {FMUMode.U_STEP }) \<and> ((pre_fmusSynchronized fmus) \<and> (pre_timeAdvanced fmus   oldFMUs   (False::\<bool>))))
		 else
			undefined
		)
		))"


\<comment>\<open>VDM source: post_postCosimulationStep: (Scenario * set1 of (FMU) * bool +> bool)
	post_postCosimulationStep(scenario, oldFMUs, RESULT) ==
null\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1750:5\<close>
definition
	post_postCosimulationStep :: "Scenario \<Rightarrow> FMU VDMSet1 \<Rightarrow> bool \<Rightarrow> bool"
where
	"post_postCosimulationStep scenario   oldFMUs   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_postCosimulationStep` specification.\<close>
		(inv_Scenario scenario  \<and>  (inv_VDMSet1' inv_FMU  oldFMUs)  \<and>  (inv_bool RESULT))"

definition
	postCosimulationStep :: "Scenario \<Rightarrow> FMU VDMSet1 \<Rightarrow> bool"
where
	"postCosimulationStep scenario   oldFMUs \<equiv> 
	\<comment>\<open>User defined body of postCosimulationStep.\<close>
	(
		let 
(fmus::FMU VDMSet1) = (rng (fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o scenario))
		in
			(if ((inv_VDMSet1' inv_FMU  fmus)) then
			((assertFMUMode fmus   {FMUMode.U_STEP }) \<and> ((variablesSynchronized scenario   {PortType.U_continous }) \<and> ((fmusSynchronized fmus) \<and> (timeAdvanced fmus   oldFMUs   (False::\<bool>)))))
		 else
			undefined
		)
		)"

	
	
\<comment>\<open>VDM source: cosimStepActions: (Connections * map (Name) to (FMU) -> seq1 of (Action))
	cosimStepActions(connections, fmus) ==
let outputs:set1 of (Action) = {mk_Action(<get>, (outputVar.name), (outputVar.ref)) | outputVar in set (dom connections) & (((outputVar.name) in set (dom fmus)) and (pre_derefOutput(fmus((outputVar.name)), (outputVar.ref)) and ((derefOutput(fmus((outputVar.name)), (outputVar.ref)).type) = <continous>)))}, inputs:set1 of (Action) = {mk_Action(<set>, (inputVar.name), (inputVar.ref)) | inputVar in set (rng connections) & (((inputVar.name) in set (dom fmus)) and (pre_derefInput(fmus((inputVar.name)), (inputVar.ref)) and ((derefInput(fmus((inputVar.name)), (inputVar.ref)).type) = <continous>)))}, steps:set1 of (Action) = {mk_Action(<step>, (fmu.name), 1) | fmu in set (rng fmus)} in let actions:seq1 of (Action) = [act | act in set ((outputs union inputs) union steps)] in actions
	pre (({(fmuRef.name) | fmuRef in set (dom connections)} subset (dom fmus)) and ({(fmuRef.name) | fmuRef in set (rng connections)} subset (dom fmus)))
	post ((len RESULT) = (((card (dom connections)) + (card (rng connections))) + (card (dom fmus))))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1765:5\<close>

\<comment>\<open>VDM source: pre_cosimStepActions: (Connections * map (Name) to (FMU) +> bool)
	pre_cosimStepActions(connections, fmus) ==
(({(fmuRef.name) | fmuRef in set (dom connections)} subset (dom fmus)) and ({(fmuRef.name) | fmuRef in set (rng connections)} subset (dom fmus)))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1783:9\<close>
definition
	pre_cosimStepActions :: "Connections \<Rightarrow> (Name \<rightharpoonup> FMU) \<Rightarrow> bool"
where
	"pre_cosimStepActions connections   fmus \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `pre_cosimStepActions` specification.\<close>
		((inv_Connections connections)  \<and>  (inv_Map (inv_Name) inv_FMU  fmus))  \<and> 
		\<comment>\<open>User defined body of pre_cosimStepActions.\<close>
		(({ (name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f fmuRef) | fmuRef .  ((fmuRef \<in>(dom connections)))  } \<subseteq> (dom fmus)) \<and> ({ (name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f fmuRef) | fmuRef .  ((fmuRef \<in>(rng connections)))  } \<subseteq> (dom fmus)))"


\<comment>\<open>VDM source: post_cosimStepActions: (Connections * map (Name) to (FMU) * seq1 of (Action) +> bool)
	post_cosimStepActions(connections, fmus, RESULT) ==
((len RESULT) = (((card (dom connections)) + (card (rng connections))) + (card (dom fmus))))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1785:20\<close>
definition
	post_cosimStepActions :: "Connections \<Rightarrow> (Name \<rightharpoonup> FMU) \<Rightarrow> Action VDMSeq1 \<Rightarrow> bool"
where
	"post_cosimStepActions connections   fmus   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `post_cosimStepActions` specification.\<close>
		((inv_Connections connections)  \<and>  (inv_Map (inv_Name) inv_FMU  fmus)  \<and>  (inv_VDMSeq1' inv_Action  RESULT))  \<and> 
		\<comment>\<open>User defined body of post_cosimStepActions.\<close>
		((len RESULT) = (((vdm_card (dom connections)) + (vdm_card (rng connections))) + (vdm_card (dom fmus))))"

definition
	cosimStepActions :: "Connections \<Rightarrow> (Name \<rightharpoonup> FMU) \<Rightarrow> Action VDMSeq1"
where
	"cosimStepActions connections   fmus \<equiv> 
	\<comment>\<open>User defined body of cosimStepActions.\<close>
	(
		let 
(outputs::Action VDMSet1) = { \<lparr>actionType\<^sub>A\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n = U_get ActionType.U_get , fmu\<^sub>A\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n = (name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f outputVar), port\<^sub>A\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n = (ref\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f outputVar)\<rparr> | outputVar .  ((outputVar \<in>(dom connections)))  \<and> (((name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f outputVar) \<in> (dom fmus)) \<and> ((pre_derefOutput (fmus (name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f outputVar))   (ref\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f outputVar)) \<and> ((type\<^sub>V\<^sub>a\<^sub>r\<^sub>i\<^sub>a\<^sub>b\<^sub>l\<^sub>e (derefOutput (fmus (name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f outputVar))   (ref\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f outputVar))) = PortType.U_continous ))) }
		;
		
(inputs::Action VDMSet1) = { \<lparr>actionType\<^sub>A\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n = U_set ActionType.U_set , fmu\<^sub>A\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n = (name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f inputVar), port\<^sub>A\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n = (ref\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f inputVar)\<rparr> | inputVar .  ((inputVar \<in>(rng connections)))  \<and> (((name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f inputVar) \<in> (dom fmus)) \<and> ((pre_derefInput (fmus (name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f inputVar))   (ref\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f inputVar)) \<and> ((type\<^sub>V\<^sub>a\<^sub>r\<^sub>i\<^sub>a\<^sub>b\<^sub>l\<^sub>e (derefInput (fmus (name\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f inputVar))   (ref\<^sub>F\<^sub>M\<^sub>U\<^sub>R\<^sub>e\<^sub>f inputVar))) = PortType.U_continous ))) }
		;
		
(steps::Action VDMSet1) = { \<lparr>actionType\<^sub>A\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n = U_step ActionType.U_step , fmu\<^sub>A\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n = (name\<^sub>F\<^sub>M\<^sub>U fmu), port\<^sub>A\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n = (1::VDMNat1)\<rparr> | fmu .  ((fmu \<in>(rng fmus)))  }
		in
			(if ((inv_VDMSet1' inv_Action  outputs))
	 \<and> 
	((inv_VDMSet1' inv_Action  inputs))
	 \<and> 
	((inv_VDMSet1' inv_Action  steps)) then
			(
		let 
(actions::Action VDMSeq1) = [ act . act \<leftarrow> sorted_list_of_set (((outputs \<union> inputs) \<union> steps)) , ((act \<in>((outputs \<union> inputs) \<union> steps))) ]
	\<comment>\<open>`Set bind `(act \<in> ((outputs \<union> inputs) \<union> steps))` in sequence comprehension requires its Isabelle type to instantiate class linorder.`   This can be a problem if the target type of @{term \<open>((outputs \<union> inputs) \<union> steps)\<close>}   has a VDM ord_ predicate.\<close> 
		in
			(if ((inv_VDMSeq1' inv_Action  actions)) then
			actions
		 else
			undefined
		)
		)
		 else
			undefined
		)
		)"

	
	
\<comment>\<open>VDM source: cosimStep: (Importer -> Importer)
	cosimStep(I) ==
let actions:seq1 of (Action) = cosimStepActions((((I.scenario).connections).dataConnections), ((I.scenario).fmus)) in runAlgorithm(I, actions)
	pre (pre_preCoSimulationStep((I.scenario), (I.time)) and (preCoSimulationStep((I.scenario), (I.time)) and (pre_cosimStepActions((((I.scenario).connections).dataConnections), ((I.scenario).fmus)) and pre_runAlgorithm(I, cosimStepActions((((I.scenario).connections).dataConnections), ((I.scenario).fmus))))))
	post (pre_postCosimulationStep((RESULT.scenario), (rng ((I.scenario).fmus))) and postCosimulationStep((RESULT.scenario), (rng ((I.scenario).fmus))))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1793:5\<close>

\<comment>\<open>VDM source: pre_cosimStep: (Importer +> bool)
	pre_cosimStep(I) ==
(pre_preCoSimulationStep((I.scenario), (I.time)) and (preCoSimulationStep((I.scenario), (I.time)) and (pre_cosimStepActions((((I.scenario).connections).dataConnections), ((I.scenario).fmus)) and pre_runAlgorithm(I, cosimStepActions((((I.scenario).connections).dataConnections), ((I.scenario).fmus))))))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1803:9\<close>
definition
	pre_cosimStep :: "Importer \<Rightarrow> bool"
where
	"pre_cosimStep I \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `pre_cosimStep` specification.\<close>
		(inv_Importer I)  \<and> 
		\<comment>\<open>User defined body of pre_cosimStep.\<close>
		((pre_preCoSimulationStep (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)   (time\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) \<and> ((preCoSimulationStep (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)   (time\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) \<and> ((pre_cosimStepActions (dataConnections\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o\<^sub>C\<^sub>o\<^sub>n\<^sub>n\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n\<^sub>s (connections\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)))   (fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I))) \<and> (pre_runAlgorithm I   (cosimStepActions (dataConnections\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o\<^sub>C\<^sub>o\<^sub>n\<^sub>n\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n\<^sub>s (connections\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)))   (fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)))))))"


\<comment>\<open>VDM source: post_cosimStep: (Importer * Importer +> bool)
	post_cosimStep(I, RESULT) ==
(pre_postCosimulationStep((RESULT.scenario), (rng ((I.scenario).fmus))) and postCosimulationStep((RESULT.scenario), (rng ((I.scenario).fmus))))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1809:13\<close>
definition
	post_cosimStep :: "Importer \<Rightarrow> Importer \<Rightarrow> bool"
where
	"post_cosimStep I   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `post_cosimStep` specification.\<close>
		(inv_Importer I  \<and>  inv_Importer RESULT)  \<and> 
		\<comment>\<open>User defined body of post_cosimStep.\<close>
		((pre_postCosimulationStep (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r RESULT)   (rng (fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)))) \<and> (postCosimulationStep (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r RESULT)   (rng (fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)))))"

definition
	cosimStep :: "Importer \<Rightarrow> Importer"
where
	"cosimStep I \<equiv> 
	\<comment>\<open>User defined body of cosimStep.\<close>
	(
		let 
(actions::Action VDMSeq1) = (cosimStepActions (dataConnections\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o\<^sub>C\<^sub>o\<^sub>n\<^sub>n\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n\<^sub>s (connections\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)))   (fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)))
		in
			(if ((inv_VDMSeq1' inv_Action  actions)) then
			(runAlgorithm I   actions)
		 else
			undefined
		)
		)"

	
	
\<comment>\<open>VDM source: preTermination: (Importer -> bool)
	preTermination(I) ==
(preCoSimulationStep((I.scenario), (I.endtime)) and ((((I.time).r) = ((I.endtime).r)) and ((I.fmusWithEvent) = {})))
	pre pre_preCoSimulationStep((I.scenario), (I.endtime))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1811:5\<close>

\<comment>\<open>VDM source: pre_preTermination: (Importer +> bool)
	pre_preTermination(I) ==
pre_preCoSimulationStep((I.scenario), (I.endtime))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1816:9\<close>
definition
	pre_preTermination :: "Importer \<Rightarrow> bool"
where
	"pre_preTermination I \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `pre_preTermination` specification.\<close>
		(inv_Importer I)  \<and> 
		\<comment>\<open>User defined body of pre_preTermination.\<close>
		(pre_preCoSimulationStep (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)   (endtime\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I))"


\<comment>\<open>VDM source: post_preTermination: (Importer * bool +> bool)
	post_preTermination(I, RESULT) ==
null\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1811:5\<close>
definition
	post_preTermination :: "Importer \<Rightarrow> bool \<Rightarrow> bool"
where
	"post_preTermination I   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_preTermination` specification.\<close>
		(inv_Importer I  \<and>  (inv_bool RESULT))"

definition
	preTermination :: "Importer \<Rightarrow> bool"
where
	"preTermination I \<equiv> 
	\<comment>\<open>User defined body of preTermination.\<close>
	((preCoSimulationStep (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)   (endtime\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) \<and> (((r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) = (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (endtime\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I))) \<and> ((fmusWithEvent\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I) = {})))"

	
	
\<comment>\<open>VDM source: postTermination: (Importer * Importer -> bool)
	postTermination(I, oldI) ==
(assertFMUMode((rng ((I.scenario).fmus)), {<DONE>}) and (fmusSynchronized((rng ((I.scenario).fmus))) and ImporterNotAffected(oldI, I)))
	pre (pre_assertFMUMode((rng ((I.scenario).fmus)), {<DONE>}) and (pre_fmusSynchronized((rng ((I.scenario).fmus))) and pre_ImporterNotAffected(oldI, I)))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1819:5\<close>

\<comment>\<open>VDM source: pre_postTermination: (Importer * Importer +> bool)
	pre_postTermination(I, oldI) ==
(pre_assertFMUMode((rng ((I.scenario).fmus)), {<DONE>}) and (pre_fmusSynchronized((rng ((I.scenario).fmus))) and pre_ImporterNotAffected(oldI, I)))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1826:13\<close>
definition
	pre_postTermination :: "Importer \<Rightarrow> Importer \<Rightarrow> bool"
where
	"pre_postTermination I   oldI \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `pre_postTermination` specification.\<close>
		(inv_Importer I  \<and>  inv_Importer oldI)  \<and> 
		\<comment>\<open>User defined body of pre_postTermination.\<close>
		((pre_assertFMUMode (rng (fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)))   {FMUMode.U_DONE }) \<and> ((pre_fmusSynchronized (rng (fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)))) \<and> (pre_ImporterNotAffected oldI   I)))"


\<comment>\<open>VDM source: post_postTermination: (Importer * Importer * bool +> bool)
	post_postTermination(I, oldI, RESULT) ==
null\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1819:5\<close>
definition
	post_postTermination :: "Importer \<Rightarrow> Importer \<Rightarrow> bool \<Rightarrow> bool"
where
	"post_postTermination I   oldI   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_postTermination` specification.\<close>
		(inv_Importer I  \<and>  inv_Importer oldI  \<and>  (inv_bool RESULT))"

definition
	postTermination :: "Importer \<Rightarrow> Importer \<Rightarrow> bool"
where
	"postTermination I   oldI \<equiv> 
	\<comment>\<open>User defined body of postTermination.\<close>
	((assertFMUMode (rng (fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)))   {FMUMode.U_DONE }) \<and> ((fmusSynchronized (rng (fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)))) \<and> (ImporterNotAffected oldI   I)))"

	
	
\<comment>\<open>VDM source: terminate: (Importer -> Importer)
	terminate(I) ==
mu(I, scenario |-> mu((I.scenario), fmus |-> {name |-> mu(((I.scenario).fmus)(name), mode |-> <DONE>) | name in set (dom ((I.scenario).fmus))}))
	pre (pre_preTermination(I) and preTermination(I))
	post (pre_postTermination(RESULT, I) and postTermination(RESULT, I))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1829:5\<close>

\<comment>\<open>VDM source: pre_terminate: (Importer +> bool)
	pre_terminate(I) ==
(pre_preTermination(I) and preTermination(I))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1834:9\<close>
definition
	pre_terminate :: "Importer \<Rightarrow> bool"
where
	"pre_terminate I \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `pre_terminate` specification.\<close>
		(inv_Importer I)  \<and> 
		\<comment>\<open>User defined body of pre_terminate.\<close>
		((pre_preTermination I) \<and> (preTermination I))"


\<comment>\<open>VDM source: post_terminate: (Importer * Importer +> bool)
	post_terminate(I, RESULT) ==
(pre_postTermination(RESULT, I) and postTermination(RESULT, I))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1837:9\<close>
definition
	post_terminate :: "Importer \<Rightarrow> Importer \<Rightarrow> bool"
where
	"post_terminate I   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `post_terminate` specification.\<close>
		(inv_Importer I  \<and>  inv_Importer RESULT)  \<and> 
		\<comment>\<open>User defined body of post_terminate.\<close>
		((pre_postTermination RESULT   I) \<and> (postTermination RESULT   I))"

definition
	terminate :: "Importer \<Rightarrow> Importer"
where
	"terminate I \<equiv> 
	\<comment>\<open>User defined body of terminate.\<close>
	(I)\<lparr>scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r := ((scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I))\<lparr>fmus\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r := (\<comment>\<open>VDM Map comprehension is translated as a lambda-term through mapCompSetBound\<close>
		mapCompSetBound 
		{ name .   ((name \<in>(dom (fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)))))  } 
		{(((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) name))\<lparr>mode\<^sub>F\<^sub>M\<^sub>U := FMUMode.U_DONE \<rparr>} 
		((inv_VDMSeq1' (inv_VDMChar))) 
		 (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U FMU))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U FMU)))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U FMU))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U FMU)))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U FMU))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U FMU))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U FMU))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U FMU)))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U FMU))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U FMU)))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U FMU)))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U FMU))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U FMU))) ) 
		(domid ) 
		(
	\<lambda> (dummy0DOMAIN :: Name)   (dummy0RANGE :: FMU) .
		(if ((((inv_VDMSeq1' (inv_VDMChar) dummy0DOMAIN))))  \<and>  (( (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) ))) \<and>  (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U (
		if ((\<exists> (dummy0RANGE :: FMU)  . ((( (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) ))) \<longrightarrow> (\<comment>\<open>Transform a VDM `=` expression into an `eq_FMU` call\<close>
	(eq_FMU dummy0RANGE   (((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) name))\<lparr>mode\<^sub>F\<^sub>M\<^sub>U := FMUMode.U_DONE \<rparr>) \<and> (True::\<bool>))))) then
		(dummy0RANGE)
		else
		(undefined))))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U (
		if ((\<exists> (dummy0RANGE :: FMU)  . ((( (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) ))) \<longrightarrow> (\<comment>\<open>Transform a VDM `=` expression into an `eq_FMU` call\<close>
	(eq_FMU dummy0RANGE   (((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) name))\<lparr>mode\<^sub>F\<^sub>M\<^sub>U := FMUMode.U_DONE \<rparr>) \<and> (True::\<bool>))))) then
		(dummy0RANGE)
		else
		(undefined)))))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U (
		if ((\<exists> (dummy0RANGE :: FMU)  . ((( (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) ))) \<longrightarrow> (\<comment>\<open>Transform a VDM `=` expression into an `eq_FMU` call\<close>
	(eq_FMU dummy0RANGE   (((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) name))\<lparr>mode\<^sub>F\<^sub>M\<^sub>U := FMUMode.U_DONE \<rparr>) \<and> (True::\<bool>))))) then
		(dummy0RANGE)
		else
		(undefined))))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U (
		if ((\<exists> (dummy0RANGE :: FMU)  . ((( (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) ))) \<longrightarrow> (\<comment>\<open>Transform a VDM `=` expression into an `eq_FMU` call\<close>
	(eq_FMU dummy0RANGE   (((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) name))\<lparr>mode\<^sub>F\<^sub>M\<^sub>U := FMUMode.U_DONE \<rparr>) \<and> (True::\<bool>))))) then
		(dummy0RANGE)
		else
		(undefined)))))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U (
		if ((\<exists> (dummy0RANGE :: FMU)  . ((( (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) ))) \<longrightarrow> (\<comment>\<open>Transform a VDM `=` expression into an `eq_FMU` call\<close>
	(eq_FMU dummy0RANGE   (((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) name))\<lparr>mode\<^sub>F\<^sub>M\<^sub>U := FMUMode.U_DONE \<rparr>) \<and> (True::\<bool>))))) then
		(dummy0RANGE)
		else
		(undefined))))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U (
		if ((\<exists> (dummy0RANGE :: FMU)  . ((( (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) ))) \<longrightarrow> (\<comment>\<open>Transform a VDM `=` expression into an `eq_FMU` call\<close>
	(eq_FMU dummy0RANGE   (((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) name))\<lparr>mode\<^sub>F\<^sub>M\<^sub>U := FMUMode.U_DONE \<rparr>) \<and> (True::\<bool>))))) then
		(dummy0RANGE)
		else
		(undefined))))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U (
		if ((\<exists> (dummy0RANGE :: FMU)  . ((( (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) ))) \<longrightarrow> (\<comment>\<open>Transform a VDM `=` expression into an `eq_FMU` call\<close>
	(eq_FMU dummy0RANGE   (((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) name))\<lparr>mode\<^sub>F\<^sub>M\<^sub>U := FMUMode.U_DONE \<rparr>) \<and> (True::\<bool>))))) then
		(dummy0RANGE)
		else
		(undefined))))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U (
		if ((\<exists> (dummy0RANGE :: FMU)  . ((( (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) ))) \<longrightarrow> (\<comment>\<open>Transform a VDM `=` expression into an `eq_FMU` call\<close>
	(eq_FMU dummy0RANGE   (((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) name))\<lparr>mode\<^sub>F\<^sub>M\<^sub>U := FMUMode.U_DONE \<rparr>) \<and> (True::\<bool>))))) then
		(dummy0RANGE)
		else
		(undefined)))))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U (
		if ((\<exists> (dummy0RANGE :: FMU)  . ((( (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) ))) \<longrightarrow> (\<comment>\<open>Transform a VDM `=` expression into an `eq_FMU` call\<close>
	(eq_FMU dummy0RANGE   (((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) name))\<lparr>mode\<^sub>F\<^sub>M\<^sub>U := FMUMode.U_DONE \<rparr>) \<and> (True::\<bool>))))) then
		(dummy0RANGE)
		else
		(undefined))))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U (
		if ((\<exists> (dummy0RANGE :: FMU)  . ((( (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) ))) \<longrightarrow> (\<comment>\<open>Transform a VDM `=` expression into an `eq_FMU` call\<close>
	(eq_FMU dummy0RANGE   (((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) name))\<lparr>mode\<^sub>F\<^sub>M\<^sub>U := FMUMode.U_DONE \<rparr>) \<and> (True::\<bool>))))) then
		(dummy0RANGE)
		else
		(undefined)))))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U (
		if ((\<exists> (dummy0RANGE :: FMU)  . ((( (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) ))) \<longrightarrow> (\<comment>\<open>Transform a VDM `=` expression into an `eq_FMU` call\<close>
	(eq_FMU dummy0RANGE   (((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) name))\<lparr>mode\<^sub>F\<^sub>M\<^sub>U := FMUMode.U_DONE \<rparr>) \<and> (True::\<bool>))))) then
		(dummy0RANGE)
		else
		(undefined)))))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U (
		if ((\<exists> (dummy0RANGE :: FMU)  . ((( (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) ))) \<longrightarrow> (\<comment>\<open>Transform a VDM `=` expression into an `eq_FMU` call\<close>
	(eq_FMU dummy0RANGE   (((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) name))\<lparr>mode\<^sub>F\<^sub>M\<^sub>U := FMUMode.U_DONE \<rparr>) \<and> (True::\<bool>))))) then
		(dummy0RANGE)
		else
		(undefined))))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U (
		if ((\<exists> (dummy0RANGE :: FMU)  . ((( (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) ))) \<longrightarrow> (\<comment>\<open>Transform a VDM `=` expression into an `eq_FMU` call\<close>
	(eq_FMU dummy0RANGE   (((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) name))\<lparr>mode\<^sub>F\<^sub>M\<^sub>U := FMUMode.U_DONE \<rparr>) \<and> (True::\<bool>))))) then
		(dummy0RANGE)
		else
		(undefined))))) ) then
			(
		if ((\<exists> (dummy0RANGE :: FMU)  . ((( (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) ))) \<longrightarrow> (\<comment>\<open>Transform a VDM `=` expression into an `eq_FMU` call\<close>
	(eq_FMU dummy0RANGE   (((fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) name))\<lparr>mode\<^sub>F\<^sub>M\<^sub>U := FMUMode.U_DONE \<rparr>) \<and> (True::\<bool>))))) then
		(dummy0RANGE)
		else
		(undefined))
		 else
			undefined
		)
		) 
		(truecnst ))\<rparr>\<rparr>"

	
	
\<comment>\<open>VDM source: stepNegotiation: (Importer -> Real1)
	stepNegotiation(I) ==
let maxSteps:set1 of (Real1) = {(fmu.maxStep) | fmu in set (rng ((I.scenario).fmus))}, scheduling:set of (Real1) = {(t - ((I.time).r)) | t in set (rng (I.schedule))}, timeLeft:Real1 = (((I.endtime).r) - ((I.time).r)), steps:set1 of (Real1) = ((maxSteps union scheduling) union {timeLeft}) in selectMinStep(steps)
	pre let maxSteps:set1 of (Real1) = {(fmu.maxStep) | fmu in set (rng ((I.scenario).fmus))}, scheduling:set of (Real1) = {(t - ((I.time).r)) | t in set (rng (I.schedule))}, timeLeft:Real1 = (((I.endtime).r) - ((I.time).r)), steps:set1 of (Real1) = ((maxSteps union scheduling) union {timeLeft}) in pre_selectMinStep(steps)
	post ((forall fmu in set (rng ((I.scenario).fmus)) & ((fmu.maxStep) >= RESULT)) and ((forall clockTicks in set (rng (I.schedule)) & ((clockTicks - ((I.time).r)) >= RESULT)) and ((RESULT <= (I.stepSize)) and (RESULT <= (((I.endtime).r) - ((I.time).r))))))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1841:5\<close>

\<comment>\<open>VDM source: pre_stepNegotiation: (Importer +> bool)
	pre_stepNegotiation(I) ==
let maxSteps:set1 of (Real1) = {(fmu.maxStep) | fmu in set (rng ((I.scenario).fmus))}, scheduling:set of (Real1) = {(t - ((I.time).r)) | t in set (rng (I.schedule))}, timeLeft:Real1 = (((I.endtime).r) - ((I.time).r)), steps:set1 of (Real1) = ((maxSteps union scheduling) union {timeLeft}) in pre_selectMinStep(steps)\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1850:9\<close>
definition
	pre_stepNegotiation :: "Importer \<Rightarrow> bool"
where
	"pre_stepNegotiation I \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `pre_stepNegotiation` specification.\<close>
		(inv_Importer I)  \<and> 
		\<comment>\<open>User defined body of pre_stepNegotiation.\<close>
		(
		let 
(maxSteps::Real1 VDMSet1) = { (maxStep\<^sub>F\<^sub>M\<^sub>U fmu) | fmu .  ((fmu \<in>(rng (fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)))))  }
		;
		
(scheduling::Real1 VDMSet) = { (t - (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I))) | t .  ((t \<in>(rng (schedule\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I))))  }
		;
		
(timeLeft::Real1) = ((r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (endtime\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) - (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)))
		;
		
(steps::Real1 VDMSet1) = ((maxSteps \<union> scheduling) \<union> {timeLeft})
		in
			(if ((inv_VDMSet1' ((inv_VDMReal)) maxSteps))
	 \<and> 
	((inv_VDMSet' ((inv_VDMReal)) scheduling))
	 \<and> 
	(((inv_VDMReal))timeLeft)
	 \<and> 
	((inv_VDMSet1' ((inv_VDMReal)) steps)) then
			(pre_selectMinStep steps)
		 else
			undefined
		)
		)"


\<comment>\<open>VDM source: post_stepNegotiation: (Importer * Real1 +> bool)
	post_stepNegotiation(I, RESULT) ==
((forall fmu in set (rng ((I.scenario).fmus)) & ((fmu.maxStep) >= RESULT)) and ((forall clockTicks in set (rng (I.schedule)) & ((clockTicks - ((I.time).r)) >= RESULT)) and ((RESULT <= (I.stepSize)) and (RESULT <= (((I.endtime).r) - ((I.time).r))))))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1857:13\<close>
definition
	post_stepNegotiation :: "Importer \<Rightarrow> Real1 \<Rightarrow> bool"
where
	"post_stepNegotiation I   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `post_stepNegotiation` specification.\<close>
		(inv_Importer I  \<and>  (inv_Real1 RESULT))  \<and> 
		\<comment>\<open>User defined body of post_stepNegotiation.\<close>
		((\<forall> fmu \<in> (rng (fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)))  . ((maxStep\<^sub>F\<^sub>M\<^sub>U fmu) \<ge> RESULT)) \<and> ((\<forall> clockTicks \<in> (rng (schedule\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I))  . ((clockTicks - (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I))) \<ge> RESULT)) \<and> ((RESULT \<le> (stepSize\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) \<and> (RESULT \<le> ((r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (endtime\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) - (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)))))))"

definition
	stepNegotiation :: "Importer \<Rightarrow> Real1"
where
	"stepNegotiation I \<equiv> 
	\<comment>\<open>User defined body of stepNegotiation.\<close>
	(
		let 
(maxSteps::Real1 VDMSet1) = { (maxStep\<^sub>F\<^sub>M\<^sub>U fmu) | fmu .  ((fmu \<in>(rng (fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)))))  }
		;
		
(scheduling::Real1 VDMSet) = { (t - (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I))) | t .  ((t \<in>(rng (schedule\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I))))  }
		;
		
(timeLeft::Real1) = ((r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (endtime\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) - (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)))
		;
		
(steps::Real1 VDMSet1) = ((maxSteps \<union> scheduling) \<union> {timeLeft})
		in
			(if ((inv_VDMSet1' ((inv_VDMReal)) maxSteps))
	 \<and> 
	((inv_VDMSet' ((inv_VDMReal)) scheduling))
	 \<and> 
	(((inv_VDMReal))timeLeft)
	 \<and> 
	((inv_VDMSet1' ((inv_VDMReal)) steps)) then
			(selectMinStep steps)
		 else
			undefined
		)
		)"

	
	
\<comment>\<open>VDM source: checkHandleEvents: (Importer -> Importer)
	checkHandleEvents(I) ==
let mk_(I1, clocksToTick):(Importer * set of (FMURef)) = tickingClocks(I), eventDetected:bool = ((clocksToTick <> {}) or ((I1.fmusWithEvent) <> {})), I2:Importer = (if eventDetected
then clockedSimulationAlgorithm(I1, clocksToTick)
else I) in I2
	pre (pre_tickingClocks(I) and let mk_(I1, clocksToTick):(Importer * set of (FMURef)) = tickingClocks(I), eventDetected:bool = ((clocksToTick <> {}) or ((I1.fmusWithEvent) <> {})) in (eventDetected => pre_clockedSimulationAlgorithm(I1, clocksToTick)))
	post (pre_tickingClocks(I) and let mk_(I1, clocksToTick):(Importer * set of (FMURef)) = tickingClocks(I), eventDetected:bool = ((clocksToTick <> {}) or ((I1.fmusWithEvent) <> {})) in (eventDetected <=> (RESULT <> I)))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1862:5\<close>

\<comment>\<open>VDM source: pre_checkHandleEvents: (Importer +> bool)
	pre_checkHandleEvents(I) ==
(pre_tickingClocks(I) and let mk_(I1, clocksToTick):(Importer * set of (FMURef)) = tickingClocks(I), eventDetected:bool = ((clocksToTick <> {}) or ((I1.fmusWithEvent) <> {})) in (eventDetected => pre_clockedSimulationAlgorithm(I1, clocksToTick)))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1876:9\<close>
definition
	pre_checkHandleEvents :: "Importer \<Rightarrow> bool"
where
	"pre_checkHandleEvents I \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `pre_checkHandleEvents` specification.\<close>
		(inv_Importer I)  \<and> 
		\<comment>\<open>User defined body of pre_checkHandleEvents.\<close>
		((pre_tickingClocks I) \<and> (
		let 
(I1::Importer) = (tickingClocks I);
(clocksToTick::FMURef VDMSet) = (tickingClocks I)
		;
		
(eventDetected::bool) = ((clocksToTick \<noteq> {}) \<or> ((fmusWithEvent\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I1) \<noteq> {}))
		in
			(if (
		( (( (((inv_Map ((inv_VDMSeq1' (inv_VDMChar))) inv_FMU  (fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r (fst dummy0))))) \<and> 
		 ((inv_VDMSet' inv_TimeBasedClock  (timeBasedClocks\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r (fst dummy0))))) \<and> 
		 (
		((((inv_Map inv_FMURef  inv_FMURef  (dataConnections\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o\<^sub>C\<^sub>o\<^sub>n\<^sub>n\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n\<^sub>s (connections\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r (fst dummy0))))))) \<and> 
		 (((inv_Map inv_FMURef  inv_FMURef  (clockConnections\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o\<^sub>C\<^sub>o\<^sub>n\<^sub>n\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n\<^sub>s (connections\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r (fst dummy0))))))) \<and> 
		 ((inv_Map ((inv_VDMSeq1' (inv_VDMChar))) (inv_VDMSet1' inv_FMURef ) (timedClockConnections\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o\<^sub>C\<^sub>o\<^sub>n\<^sub>n\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n\<^sub>s (connections\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r (fst dummy0))))))
		)) )) \<and> 
		 ((inv_Map ((inv_VDMSeq1' (inv_VDMChar))) ((inv_VDMReal)) (schedule\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r (fst dummy0)))) \<and> 
		 ((inv_VDMSet' inv_FMURef  (activeClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r (fst dummy0)))) \<and> 
		 ((inv_VDMSet' inv_FMURef  (readyClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r (fst dummy0)))) \<and> 
		 ((inv_VDMSet' inv_FMURef  (inactiveClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r (fst dummy0)))) \<and> 
		 ((inv_VDMSet' ((inv_VDMSeq1' (inv_VDMChar))) (fmusWithEvent\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r (fst dummy0)))) \<and> 
		 ((inv_VDMSet' inv_FMURef  (relevantOutputClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r (fst dummy0)))) \<and> 
		 ((inv_VDMSet' inv_FMURef  (relevantInputClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r (fst dummy0)))) \<and> 
		 ((inv_VDMSet' inv_FMURef  (activeEquations\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r (fst dummy0)))) \<and> 
		 ((inv_VDMSet' inv_FMURef  (calculatedEquations\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r (fst dummy0)))) \<and> 
		 ((inv_VDMSet' inv_FMURef  (readyEquations\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r (fst dummy0)))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r (fst dummy0)))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r (fst dummy0))))) )) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (endtime\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r (fst dummy0)))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (endtime\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r (fst dummy0))))) )) \<and> 
		 (((inv_VDMReal (stepSize\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r (fst dummy0))))) \<and> 
		 ((inv_Map inv_FMURef  inv_FMIValue  (valueMap\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r (fst dummy0)))) )\<and>
		 (inv_VDMSet' inv_FMURef  (snd dummy0))
		))
	 \<and> 
	((inv_bool eventDetected)) then
			(eventDetected \<longrightarrow> (pre_clockedSimulationAlgorithm I1   clocksToTick))
		 else
			undefined
		)
		))"


\<comment>\<open>VDM source: post_checkHandleEvents: (Importer * Importer +> bool)
	post_checkHandleEvents(I, RESULT) ==
(pre_tickingClocks(I) and let mk_(I1, clocksToTick):(Importer * set of (FMURef)) = tickingClocks(I), eventDetected:bool = ((clocksToTick <> {}) or ((I1.fmusWithEvent) <> {})) in (eventDetected <=> (RESULT <> I)))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1884:9\<close>
definition
	post_checkHandleEvents :: "Importer \<Rightarrow> Importer \<Rightarrow> bool"
where
	"post_checkHandleEvents I   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `post_checkHandleEvents` specification.\<close>
		(inv_Importer I  \<and>  inv_Importer RESULT)  \<and> 
		\<comment>\<open>User defined body of post_checkHandleEvents.\<close>
		((pre_tickingClocks I) \<and> (
		let 
(I1::Importer) = (tickingClocks I);
(clocksToTick::FMURef VDMSet) = (tickingClocks I)
		;
		
(eventDetected::bool) = ((clocksToTick \<noteq> {}) \<or> ((fmusWithEvent\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I1) \<noteq> {}))
		in
			(if (
		( (( (((inv_Map ((inv_VDMSeq1' (inv_VDMChar))) inv_FMU  (fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r (fst dummy0))))) \<and> 
		 ((inv_VDMSet' inv_TimeBasedClock  (timeBasedClocks\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r (fst dummy0))))) \<and> 
		 (
		((((inv_Map inv_FMURef  inv_FMURef  (dataConnections\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o\<^sub>C\<^sub>o\<^sub>n\<^sub>n\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n\<^sub>s (connections\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r (fst dummy0))))))) \<and> 
		 (((inv_Map inv_FMURef  inv_FMURef  (clockConnections\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o\<^sub>C\<^sub>o\<^sub>n\<^sub>n\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n\<^sub>s (connections\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r (fst dummy0))))))) \<and> 
		 ((inv_Map ((inv_VDMSeq1' (inv_VDMChar))) (inv_VDMSet1' inv_FMURef ) (timedClockConnections\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o\<^sub>C\<^sub>o\<^sub>n\<^sub>n\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n\<^sub>s (connections\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r (fst dummy0))))))
		)) )) \<and> 
		 ((inv_Map ((inv_VDMSeq1' (inv_VDMChar))) ((inv_VDMReal)) (schedule\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r (fst dummy0)))) \<and> 
		 ((inv_VDMSet' inv_FMURef  (activeClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r (fst dummy0)))) \<and> 
		 ((inv_VDMSet' inv_FMURef  (readyClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r (fst dummy0)))) \<and> 
		 ((inv_VDMSet' inv_FMURef  (inactiveClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r (fst dummy0)))) \<and> 
		 ((inv_VDMSet' ((inv_VDMSeq1' (inv_VDMChar))) (fmusWithEvent\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r (fst dummy0)))) \<and> 
		 ((inv_VDMSet' inv_FMURef  (relevantOutputClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r (fst dummy0)))) \<and> 
		 ((inv_VDMSet' inv_FMURef  (relevantInputClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r (fst dummy0)))) \<and> 
		 ((inv_VDMSet' inv_FMURef  (activeEquations\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r (fst dummy0)))) \<and> 
		 ((inv_VDMSet' inv_FMURef  (calculatedEquations\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r (fst dummy0)))) \<and> 
		 ((inv_VDMSet' inv_FMURef  (readyEquations\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r (fst dummy0)))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r (fst dummy0)))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r (fst dummy0))))) )) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (endtime\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r (fst dummy0)))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (endtime\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r (fst dummy0))))) )) \<and> 
		 (((inv_VDMReal (stepSize\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r (fst dummy0))))) \<and> 
		 ((inv_Map inv_FMURef  inv_FMIValue  (valueMap\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r (fst dummy0)))) )\<and>
		 (inv_VDMSet' inv_FMURef  (snd dummy0))
		))
	 \<and> 
	((inv_bool eventDetected)) then
			(eventDetected \<longleftrightarrow> (RESULT \<noteq> I))
		 else
			undefined
		)
		))"

definition
	checkHandleEvents :: "Importer \<Rightarrow> Importer"
where
	"checkHandleEvents I \<equiv> 
	\<comment>\<open>User defined body of checkHandleEvents.\<close>
	(
		let 
(clocksToTick::FMURef VDMSet) = (tickingClocks I);
(I1::Importer) = (tickingClocks I)
		;
		
(eventDetected::bool) = ((clocksToTick \<noteq> {}) \<or> ((fmusWithEvent\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I1) \<noteq> {}))
		;
		
(I2::Importer) = (
		if (eventDetected) then
		((clockedSimulationAlgorithm I1   clocksToTick))
		else
		(I))
		in
			(if (
		( (( (((inv_Map ((inv_VDMSeq1' (inv_VDMChar))) inv_FMU  (fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r (fst dummy0))))) \<and> 
		 ((inv_VDMSet' inv_TimeBasedClock  (timeBasedClocks\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r (fst dummy0))))) \<and> 
		 (
		((((inv_Map inv_FMURef  inv_FMURef  (dataConnections\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o\<^sub>C\<^sub>o\<^sub>n\<^sub>n\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n\<^sub>s (connections\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r (fst dummy0))))))) \<and> 
		 (((inv_Map inv_FMURef  inv_FMURef  (clockConnections\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o\<^sub>C\<^sub>o\<^sub>n\<^sub>n\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n\<^sub>s (connections\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r (fst dummy0))))))) \<and> 
		 ((inv_Map ((inv_VDMSeq1' (inv_VDMChar))) (inv_VDMSet1' inv_FMURef ) (timedClockConnections\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o\<^sub>C\<^sub>o\<^sub>n\<^sub>n\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n\<^sub>s (connections\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r (fst dummy0))))))
		)) )) \<and> 
		 ((inv_Map ((inv_VDMSeq1' (inv_VDMChar))) ((inv_VDMReal)) (schedule\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r (fst dummy0)))) \<and> 
		 ((inv_VDMSet' inv_FMURef  (activeClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r (fst dummy0)))) \<and> 
		 ((inv_VDMSet' inv_FMURef  (readyClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r (fst dummy0)))) \<and> 
		 ((inv_VDMSet' inv_FMURef  (inactiveClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r (fst dummy0)))) \<and> 
		 ((inv_VDMSet' ((inv_VDMSeq1' (inv_VDMChar))) (fmusWithEvent\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r (fst dummy0)))) \<and> 
		 ((inv_VDMSet' inv_FMURef  (relevantOutputClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r (fst dummy0)))) \<and> 
		 ((inv_VDMSet' inv_FMURef  (relevantInputClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r (fst dummy0)))) \<and> 
		 ((inv_VDMSet' inv_FMURef  (activeEquations\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r (fst dummy0)))) \<and> 
		 ((inv_VDMSet' inv_FMURef  (calculatedEquations\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r (fst dummy0)))) \<and> 
		 ((inv_VDMSet' inv_FMURef  (readyEquations\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r (fst dummy0)))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r (fst dummy0)))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r (fst dummy0))))) )) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (endtime\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r (fst dummy0)))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (endtime\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r (fst dummy0))))) )) \<and> 
		 (((inv_VDMReal (stepSize\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r (fst dummy0))))) \<and> 
		 ((inv_Map inv_FMURef  inv_FMIValue  (valueMap\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r (fst dummy0)))) )\<and>
		 (inv_VDMSet' inv_FMURef  (snd dummy0))
		))
	 \<and> 
	((inv_bool eventDetected))
	 \<and> 
	(inv_Importer I2) then
			I2
		 else
			undefined
		)
		)"

	
	
\<comment>\<open>VDM source: updateScenarioAfterStep: (Importer -> Importer)
	updateScenarioAfterStep(I) ==
let fmus:map (Name) to (FMU) = ((I.scenario).fmus) in mu(I, scenario |-> mu((I.scenario), fmus |-> {name |-> mu(fmus(name), stepped |-> false) | name in set (dom fmus)}), time |-> mk_Time((((I.time).r) + (I.stepSize)), ((I.time).i)))
	pre (forall fmu in set (rng ((I.scenario).fmus)) & (fmu.stepped))
	post (((((I.time).r) + (I.stepSize)) = ((RESULT.time).r)) and (forall fmu in set (rng ((RESULT.scenario).fmus)) & (not (fmu.stepped))))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1891:5\<close>

\<comment>\<open>VDM source: pre_updateScenarioAfterStep: (Importer +> bool)
	pre_updateScenarioAfterStep(I) ==
(forall fmu in set (rng ((I.scenario).fmus)) & (fmu.stepped))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1903:9\<close>
definition
	pre_updateScenarioAfterStep :: "Importer \<Rightarrow> bool"
where
	"pre_updateScenarioAfterStep I \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `pre_updateScenarioAfterStep` specification.\<close>
		(inv_Importer I)  \<and> 
		\<comment>\<open>User defined body of pre_updateScenarioAfterStep.\<close>
		(\<forall> fmu \<in> (rng (fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)))  . (stepped\<^sub>F\<^sub>M\<^sub>U fmu))"


\<comment>\<open>VDM source: post_updateScenarioAfterStep: (Importer * Importer +> bool)
	post_updateScenarioAfterStep(I, RESULT) ==
(((((I.time).r) + (I.stepSize)) = ((RESULT.time).r)) and (forall fmu in set (rng ((RESULT.scenario).fmus)) & (not (fmu.stepped))))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1906:9\<close>
definition
	post_updateScenarioAfterStep :: "Importer \<Rightarrow> Importer \<Rightarrow> bool"
where
	"post_updateScenarioAfterStep I   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `post_updateScenarioAfterStep` specification.\<close>
		(inv_Importer I  \<and>  inv_Importer RESULT)  \<and> 
		\<comment>\<open>User defined body of post_updateScenarioAfterStep.\<close>
		((((r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) + (stepSize\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) = (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r RESULT))) \<and> (\<forall> fmu \<in> (rng (fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r RESULT)))  . (\<not> (stepped\<^sub>F\<^sub>M\<^sub>U fmu))))"

definition
	updateScenarioAfterStep :: "Importer \<Rightarrow> Importer"
where
	"updateScenarioAfterStep I \<equiv> 
	\<comment>\<open>User defined body of updateScenarioAfterStep.\<close>
	(
		let 
(fmus::(Name \<rightharpoonup> FMU)) = (fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I))
		in
			(if ((inv_Map ((inv_VDMSeq1' (inv_VDMChar))) inv_FMU  fmus)) then
			(I)\<lparr>scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r := ((scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I))\<lparr>fmus\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r := (\<comment>\<open>VDM Map comprehension is translated as a lambda-term through mapCompSetBound\<close>
		mapCompSetBound 
		{ name .   ((name \<in>(dom fmus)))  } 
		{((fmus name))\<lparr>stepped\<^sub>F\<^sub>M\<^sub>U := (False::\<bool>)\<rparr>} 
		((inv_VDMSeq1' (inv_VDMChar))) 
		 (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U FMU))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U FMU)))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U FMU))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U FMU)))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U FMU))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U FMU))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U FMU))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U FMU)))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U FMU))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U FMU)))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U FMU)))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U FMU))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U FMU))) ) 
		(domid ) 
		(
	\<lambda> (dummy0DOMAIN :: Name)   (dummy0RANGE :: FMU) .
		(if ((((inv_VDMSeq1' (inv_VDMChar) dummy0DOMAIN))))  \<and>  (( (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) ))) \<and>  (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U (
		if ((\<exists> (dummy0RANGE :: FMU)  . ((( (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) ))) \<longrightarrow> (\<comment>\<open>Transform a VDM `=` expression into an `eq_FMU` call\<close>
	(eq_FMU dummy0RANGE   ((fmus name))\<lparr>stepped\<^sub>F\<^sub>M\<^sub>U := (False::\<bool>)\<rparr>) \<and> (True::\<bool>))))) then
		(dummy0RANGE)
		else
		(undefined))))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U (
		if ((\<exists> (dummy0RANGE :: FMU)  . ((( (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) ))) \<longrightarrow> (\<comment>\<open>Transform a VDM `=` expression into an `eq_FMU` call\<close>
	(eq_FMU dummy0RANGE   ((fmus name))\<lparr>stepped\<^sub>F\<^sub>M\<^sub>U := (False::\<bool>)\<rparr>) \<and> (True::\<bool>))))) then
		(dummy0RANGE)
		else
		(undefined)))))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U (
		if ((\<exists> (dummy0RANGE :: FMU)  . ((( (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) ))) \<longrightarrow> (\<comment>\<open>Transform a VDM `=` expression into an `eq_FMU` call\<close>
	(eq_FMU dummy0RANGE   ((fmus name))\<lparr>stepped\<^sub>F\<^sub>M\<^sub>U := (False::\<bool>)\<rparr>) \<and> (True::\<bool>))))) then
		(dummy0RANGE)
		else
		(undefined))))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U (
		if ((\<exists> (dummy0RANGE :: FMU)  . ((( (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) ))) \<longrightarrow> (\<comment>\<open>Transform a VDM `=` expression into an `eq_FMU` call\<close>
	(eq_FMU dummy0RANGE   ((fmus name))\<lparr>stepped\<^sub>F\<^sub>M\<^sub>U := (False::\<bool>)\<rparr>) \<and> (True::\<bool>))))) then
		(dummy0RANGE)
		else
		(undefined)))))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U (
		if ((\<exists> (dummy0RANGE :: FMU)  . ((( (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) ))) \<longrightarrow> (\<comment>\<open>Transform a VDM `=` expression into an `eq_FMU` call\<close>
	(eq_FMU dummy0RANGE   ((fmus name))\<lparr>stepped\<^sub>F\<^sub>M\<^sub>U := (False::\<bool>)\<rparr>) \<and> (True::\<bool>))))) then
		(dummy0RANGE)
		else
		(undefined))))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U (
		if ((\<exists> (dummy0RANGE :: FMU)  . ((( (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) ))) \<longrightarrow> (\<comment>\<open>Transform a VDM `=` expression into an `eq_FMU` call\<close>
	(eq_FMU dummy0RANGE   ((fmus name))\<lparr>stepped\<^sub>F\<^sub>M\<^sub>U := (False::\<bool>)\<rparr>) \<and> (True::\<bool>))))) then
		(dummy0RANGE)
		else
		(undefined))))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U (
		if ((\<exists> (dummy0RANGE :: FMU)  . ((( (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) ))) \<longrightarrow> (\<comment>\<open>Transform a VDM `=` expression into an `eq_FMU` call\<close>
	(eq_FMU dummy0RANGE   ((fmus name))\<lparr>stepped\<^sub>F\<^sub>M\<^sub>U := (False::\<bool>)\<rparr>) \<and> (True::\<bool>))))) then
		(dummy0RANGE)
		else
		(undefined))))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U (
		if ((\<exists> (dummy0RANGE :: FMU)  . ((( (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) ))) \<longrightarrow> (\<comment>\<open>Transform a VDM `=` expression into an `eq_FMU` call\<close>
	(eq_FMU dummy0RANGE   ((fmus name))\<lparr>stepped\<^sub>F\<^sub>M\<^sub>U := (False::\<bool>)\<rparr>) \<and> (True::\<bool>))))) then
		(dummy0RANGE)
		else
		(undefined)))))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U (
		if ((\<exists> (dummy0RANGE :: FMU)  . ((( (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) ))) \<longrightarrow> (\<comment>\<open>Transform a VDM `=` expression into an `eq_FMU` call\<close>
	(eq_FMU dummy0RANGE   ((fmus name))\<lparr>stepped\<^sub>F\<^sub>M\<^sub>U := (False::\<bool>)\<rparr>) \<and> (True::\<bool>))))) then
		(dummy0RANGE)
		else
		(undefined))))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U (
		if ((\<exists> (dummy0RANGE :: FMU)  . ((( (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) ))) \<longrightarrow> (\<comment>\<open>Transform a VDM `=` expression into an `eq_FMU` call\<close>
	(eq_FMU dummy0RANGE   ((fmus name))\<lparr>stepped\<^sub>F\<^sub>M\<^sub>U := (False::\<bool>)\<rparr>) \<and> (True::\<bool>))))) then
		(dummy0RANGE)
		else
		(undefined)))))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U (
		if ((\<exists> (dummy0RANGE :: FMU)  . ((( (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) ))) \<longrightarrow> (\<comment>\<open>Transform a VDM `=` expression into an `eq_FMU` call\<close>
	(eq_FMU dummy0RANGE   ((fmus name))\<lparr>stepped\<^sub>F\<^sub>M\<^sub>U := (False::\<bool>)\<rparr>) \<and> (True::\<bool>))))) then
		(dummy0RANGE)
		else
		(undefined)))))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U (
		if ((\<exists> (dummy0RANGE :: FMU)  . ((( (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) ))) \<longrightarrow> (\<comment>\<open>Transform a VDM `=` expression into an `eq_FMU` call\<close>
	(eq_FMU dummy0RANGE   ((fmus name))\<lparr>stepped\<^sub>F\<^sub>M\<^sub>U := (False::\<bool>)\<rparr>) \<and> (True::\<bool>))))) then
		(dummy0RANGE)
		else
		(undefined))))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U (
		if ((\<exists> (dummy0RANGE :: FMU)  . ((( (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) ))) \<longrightarrow> (\<comment>\<open>Transform a VDM `=` expression into an `eq_FMU` call\<close>
	(eq_FMU dummy0RANGE   ((fmus name))\<lparr>stepped\<^sub>F\<^sub>M\<^sub>U := (False::\<bool>)\<rparr>) \<and> (True::\<bool>))))) then
		(dummy0RANGE)
		else
		(undefined))))) ) then
			(
		if ((\<exists> (dummy0RANGE :: FMU)  . ((( (((inv_VDMNat (id\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMSeq1' (inv_VDMChar) (name\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Clock  (clocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (
		(((inv_VDMSet' inv_Variable  (LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' inv_Variable  (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))
		)) \<and> 
		 ((((inv_True (mode\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ( ((((inv_VDMReal (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))))) \<and> 
		 ((inv_VDMNat (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) )) \<and> 
		 ((inv_bool (stepped\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 (((inv_VDMReal (maxStep\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 (((inv_Map ((inv_VDMNat)) inv_FMIValue  (env\<^sub>F\<^sub>M\<^sub>U dummy0RANGE)))) \<and> 
		 ((inv_VDMSet' ((inv_VDMNat)) (activeClocks\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) \<and> 
		 ((inv_VDMSet' ((inv_Lambda ((inv_Map ((inv_VDMNat)) inv_FMIValue )) ((inv_Map ((inv_VDMNat)) inv_FMIValue )))) (activeEquations\<^sub>F\<^sub>M\<^sub>U dummy0RANGE))) ))) \<longrightarrow> (\<comment>\<open>Transform a VDM `=` expression into an `eq_FMU` call\<close>
	(eq_FMU dummy0RANGE   ((fmus name))\<lparr>stepped\<^sub>F\<^sub>M\<^sub>U := (False::\<bool>)\<rparr>) \<and> (True::\<bool>))))) then
		(dummy0RANGE)
		else
		(undefined))
		 else
			undefined
		)
		) 
		(truecnst ))\<rparr>, time\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r := \<lparr>r\<^sub>T\<^sub>i\<^sub>m\<^sub>e = ((r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) + (stepSize\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)), i\<^sub>T\<^sub>i\<^sub>m\<^sub>e = (i\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I))\<rparr>\<rparr>
		 else
			undefined
		)
		)"

	
	
\<comment>\<open>VDM source: cosimulationStep: (Importer -> Importer)
	cosimulationStep(I) ==
let I1:Importer = checkHandleEvents(I), I2:Importer = mu(I1, stepSize |-> stepNegotiation(I1)), I3:Importer = cosimStep(I2), I4:Importer = updateScenarioAfterStep(I3) in (if ((I4.endtime) > (I4.time))
then cosimulationStep(I4)
else I4)
	pre (pre_preCoSimulationStep((I.scenario), (I.time)) and (preCoSimulationStep((I.scenario), (I.time)) and (pre_checkHandleEvents(I) and let I1:Importer = checkHandleEvents(I) in (pre_stepNegotiation(I1) and let I2:Importer = mu(I1, stepSize |-> stepNegotiation(I1)) in (pre_cosimStep(I2) and let I3:Importer = cosimStep(I2) in (pre_updateScenarioAfterStep(I3) and let I4:Importer = updateScenarioAfterStep(I3) in (((I4.endtime) > (I4.time)) => pre_cosimulationStep(I4))))))))
	post (pre_preCoSimulationStep((RESULT.scenario), (RESULT.time)) and (preCoSimulationStep((RESULT.scenario), (RESULT.time)) and ((((I.time).r) <= ((RESULT.time).r)) and (pre_ImporterNotAffected(I, RESULT) and (ImporterNotAffected(I, RESULT) and let M':set1 of (FMU) = (rng ((RESULT.scenario).fmus)), M:set1 of (FMU) = (rng ((I.scenario).fmus)) in (pre_timeAdvanced(M', M, false) and timeAdvanced(M', M, false)))))))
	measure (((I.endtime).r) - ((I.time).r))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1912:5\<close>

\<comment>\<open>VDM source: pre_cosimulationStep: (Importer +> bool)
	pre_cosimulationStep(I) ==
(pre_preCoSimulationStep((I.scenario), (I.time)) and (preCoSimulationStep((I.scenario), (I.time)) and (pre_checkHandleEvents(I) and let I1:Importer = checkHandleEvents(I) in (pre_stepNegotiation(I1) and let I2:Importer = mu(I1, stepSize |-> stepNegotiation(I1)) in (pre_cosimStep(I2) and let I3:Importer = cosimStep(I2) in (pre_updateScenarioAfterStep(I3) and let I4:Importer = updateScenarioAfterStep(I3) in (((I4.endtime) > (I4.time)) => pre_cosimulationStep(I4))))))))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1937:9\<close>
definition
	pre_cosimulationStep :: "Importer \<Rightarrow> bool"
where
	"pre_cosimulationStep I \<equiv> 
	\<comment>\<open>Implicitly defined type invariant checks for  `pre_cosimulationStep` specification.\<close>
	(inv_Importer I)  \<and> 
	\<comment>\<open>User defined body of pre_cosimulationStep.\<close>
	((pre_preCoSimulationStep (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)   (time\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) \<and> ((preCoSimulationStep (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)   (time\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) \<and> ((pre_checkHandleEvents I) \<and> (
		let 
(I1::Importer) = (checkHandleEvents I)
		in
			(if (inv_Importer I1) then
			((pre_stepNegotiation I1) \<and> (
		let 
(I2::Importer) = (I1)\<lparr>stepSize\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r := (stepNegotiation I1)\<rparr>
		in
			(if (inv_Importer I2) then
			((pre_cosimStep I2) \<and> (
		let 
(I3::Importer) = (cosimStep I2)
		in
			(if (inv_Importer I3) then
			((pre_updateScenarioAfterStep I3) \<and> (
		let 
(I4::Importer) = (updateScenarioAfterStep I3)
		in
			(if (inv_Importer I4) then
			(\<comment>\<open>Transform a VDM `>` expression into a reversed `ord_Time` call\<close>
	(ord_Time (time\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I4)   (endtime\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I4)) \<longrightarrow> (pre_cosimulationStep I4))
		 else
			undefined
		)
		))
		 else
			undefined
		)
		))
		 else
			undefined
		)
		))
		 else
			undefined
		)
		))))"


\<comment>\<open>VDM source: post_cosimulationStep: (Importer * Importer +> bool)
	post_cosimulationStep(I, RESULT) ==
(pre_preCoSimulationStep((RESULT.scenario), (RESULT.time)) and (preCoSimulationStep((RESULT.scenario), (RESULT.time)) and ((((I.time).r) <= ((RESULT.time).r)) and (pre_ImporterNotAffected(I, RESULT) and (ImporterNotAffected(I, RESULT) and let M':set1 of (FMU) = (rng ((RESULT.scenario).fmus)), M:set1 of (FMU) = (rng ((I.scenario).fmus)) in (pre_timeAdvanced(M', M, false) and timeAdvanced(M', M, false)))))))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1956:9\<close>
definition
	post_cosimulationStep :: "Importer \<Rightarrow> Importer \<Rightarrow> bool"
where
	"post_cosimulationStep I   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `post_cosimulationStep` specification.\<close>
		(inv_Importer I  \<and>  inv_Importer RESULT)  \<and> 
		\<comment>\<open>User defined body of post_cosimulationStep.\<close>
		((pre_preCoSimulationStep (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r RESULT)   (time\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r RESULT)) \<and> ((preCoSimulationStep (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r RESULT)   (time\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r RESULT)) \<and> (((r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)) \<le> (r\<^sub>T\<^sub>i\<^sub>m\<^sub>e (time\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r RESULT))) \<and> ((pre_ImporterNotAffected I   RESULT) \<and> ((ImporterNotAffected I   RESULT) \<and> (
		let 
(M'::FMU VDMSet1) = (rng (fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r RESULT)))
		;
		
(M::FMU VDMSet1) = (rng (fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o (scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I)))
		in
			(if ((inv_VDMSet1' inv_FMU  M'))
	 \<and> 
	((inv_VDMSet1' inv_FMU  M)) then
			((pre_timeAdvanced M'   M   (False::\<bool>)) \<and> (timeAdvanced M'   M   (False::\<bool>)))
		 else
			undefined
		)
		))))))"

fun
	cosimulationStep :: "Importer \<Rightarrow> Importer"
where
	"cosimulationStep I = 
	\<comment>\<open>User defined body of cosimulationStep.\<close>
	(
		let 
(I1::Importer) = (checkHandleEvents I)
		;
		
(I2::Importer) = (I1)\<lparr>stepSize\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r := (stepNegotiation I1)\<rparr>
		;
		
(I3::Importer) = (cosimStep I2)
		;
		
(I4::Importer) = (updateScenarioAfterStep I3)
		in
			(if (inv_Importer I1)
	 \<and> 
	(inv_Importer I2)
	 \<and> 
	(inv_Importer I3)
	 \<and> 
	(inv_Importer I4) then
			(
		if (\<comment>\<open>Transform a VDM `>` expression into a reversed `ord_Time` call\<close>
	(ord_Time (time\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I4)   (endtime\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r I4))) then
		((cosimulationStep I4))
		else
		(I4))
		 else
			undefined
		)
		)"

	
	
\<comment>\<open>VDM source: createImporter: (Scenario * Real1 * Real1 -> Importer)
	createImporter(M, endtime, stepSize) ==
let clocks:set of (FMURef) = (dunion {createFMURefs(fmu, {(c.ref) | c in set (fmu.clocks)}) | fmu in set (rng (M.fmus)) & pre_createFMURefs(fmu, {(c.ref) | c in set (fmu.clocks)})}), discreteVariables:set of (FMURef) = (dunion {createFMURefs(fmu, {(v.ref) | v in set (((fmu.io).LFinput) union ((fmu.io).LFoutput)) & ((v.type) = <discrete>)}) | fmu in set (rng (M.fmus)) & pre_createFMURefs(fmu, {(v.ref) | v in set (((fmu.io).LFinput) union ((fmu.io).LFoutput)) & ((v.type) = <discrete>)})}) in mk_Importer(M, {|->}, {}, clocks, clocks, {}, {}, {}, {}, {}, discreteVariables, mk_Time(0, 0), mk_Time(endtime, 0), stepSize, {|->})
	pre true\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1968:5\<close>

\<comment>\<open>VDM source: pre_createImporter: (Scenario * Real1 * Real1 +> bool)
	pre_createImporter(M, endtime, stepSize) ==
true\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1997:9\<close>
definition
	pre_createImporter :: "Scenario \<Rightarrow> Real1 \<Rightarrow> Real1 \<Rightarrow> bool"
where
	"pre_createImporter M   endtime   stepSize \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `pre_createImporter` specification.\<close>
		(inv_Scenario M  \<and>  (inv_Real1 endtime)  \<and>  (inv_Real1 stepSize))  \<and> 
		\<comment>\<open>User defined body of pre_createImporter.\<close>
		(True::\<bool>)"


\<comment>\<open>VDM source: post_createImporter: (Scenario * Real1 * Real1 * Importer +> bool)
	post_createImporter(M, endtime, stepSize, RESULT) ==
null\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 1968:5\<close>
definition
	post_createImporter :: "Scenario \<Rightarrow> Real1 \<Rightarrow> Real1 \<Rightarrow> Importer \<Rightarrow> bool"
where
	"post_createImporter M   endtime   stepSize   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_createImporter` specification.\<close>
		(inv_Scenario M  \<and>  (inv_Real1 endtime)  \<and>  (inv_Real1 stepSize)  \<and>  inv_Importer RESULT)"

definition
	createImporter :: "Scenario \<Rightarrow> Real1 \<Rightarrow> Real1 \<Rightarrow> Importer"
where
	"createImporter M   endtime   stepSize \<equiv> 
	\<comment>\<open>User defined body of createImporter.\<close>
	(
		let 
(clocks::FMURef VDMSet) = (\<Union> { (createFMURefs fmu   { (ref\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k c) | c .  ((c \<in>(clocks\<^sub>F\<^sub>M\<^sub>U fmu)))  }) | fmu .  ((fmu \<in>(rng (fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o M))))  \<and> (pre_createFMURefs fmu   { (ref\<^sub>C\<^sub>l\<^sub>o\<^sub>c\<^sub>k c) | c .  ((c \<in>(clocks\<^sub>F\<^sub>M\<^sub>U fmu)))  }) })
		;
		
(discreteVariables::FMURef VDMSet) = (\<Union> { (createFMURefs fmu   { (ref\<^sub>V\<^sub>a\<^sub>r\<^sub>i\<^sub>a\<^sub>b\<^sub>l\<^sub>e v) | v .  ((v \<in>((LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U fmu)) \<union> (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U fmu)))))  \<and> ((type\<^sub>V\<^sub>a\<^sub>r\<^sub>i\<^sub>a\<^sub>b\<^sub>l\<^sub>e v) = PortType.U_discrete ) }) | fmu .  ((fmu \<in>(rng (fmus\<^sub>S\<^sub>c\<^sub>e\<^sub>n\<^sub>a\<^sub>r\<^sub>i\<^sub>o M))))  \<and> (pre_createFMURefs fmu   { (ref\<^sub>V\<^sub>a\<^sub>r\<^sub>i\<^sub>a\<^sub>b\<^sub>l\<^sub>e v) | v .  ((v \<in>((LFinput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U fmu)) \<union> (LFoutput\<^sub>I\<^sub>O\<^sub>L\<^sub>e\<^sub>o (io\<^sub>F\<^sub>M\<^sub>U fmu)))))  \<and> ((type\<^sub>V\<^sub>a\<^sub>r\<^sub>i\<^sub>a\<^sub>b\<^sub>l\<^sub>e v) = PortType.U_discrete ) }) })
		in
			(if ((inv_VDMSet' inv_FMURef  clocks))
	 \<and> 
	((inv_VDMSet' inv_FMURef  discreteVariables)) then
			\<lparr>scenario\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r = M, schedule\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r = [], activeClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r = {}, readyClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r = clocks, inactiveClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r = clocks, fmusWithEvent\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r = {}, relevantOutputClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r = {}, relevantInputClocks\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r = {}, activeEquations\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r = {}, calculatedEquations\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r = {}, readyEquations\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r = discreteVariables, time\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r = \<lparr>r\<^sub>T\<^sub>i\<^sub>m\<^sub>e = (0::VDMNat), i\<^sub>T\<^sub>i\<^sub>m\<^sub>e = (0::VDMNat)\<rparr>, endtime\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r = \<lparr>r\<^sub>T\<^sub>i\<^sub>m\<^sub>e = endtime, i\<^sub>T\<^sub>i\<^sub>m\<^sub>e = (0::VDMNat)\<rparr>, stepSize\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r = stepSize, valueMap\<^sub>I\<^sub>m\<^sub>p\<^sub>o\<^sub>r\<^sub>t\<^sub>e\<^sub>r = []\<rparr>
		 else
			undefined
		)
		)"

	
	
\<comment>\<open>VDM source: runScenario: (Scenario -> Importer)
	runScenario(scenario) ==
let I:Importer = createImporter(scenario, 10, 5), I_initialed:Importer = initialization(I), I2:Importer = cosimulationStep(I_initialed) in terminate(I2)
	pre (pre_createImporter(scenario, 10, 5) and let I:Importer = createImporter(scenario, 10, 5) in (pre_initialization(I) and let I_initialed:Importer = initialization(I) in (pre_cosimulationStep(I_initialed) and let I2:Importer = cosimulationStep(I_initialed) in pre_terminate(I2))))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 2000:5\<close>

\<comment>\<open>VDM source: pre_runScenario: (Scenario +> bool)
	pre_runScenario(scenario) ==
(pre_createImporter(scenario, 10, 5) and let I:Importer = createImporter(scenario, 10, 5) in (pre_initialization(I) and let I_initialed:Importer = initialization(I) in (pre_cosimulationStep(I_initialed) and let I2:Importer = cosimulationStep(I_initialed) in pre_terminate(I2))))\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 2008:9\<close>
definition
	pre_runScenario :: "Scenario \<Rightarrow> bool"
where
	"pre_runScenario scenario \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `pre_runScenario` specification.\<close>
		(inv_Scenario scenario)  \<and> 
		\<comment>\<open>User defined body of pre_runScenario.\<close>
		((pre_createImporter scenario   (10::VDMNat1)   (5::VDMNat1)) \<and> (
		let 
(I::Importer) = (createImporter scenario   (10::VDMNat1)   (5::VDMNat1))
		in
			(if (inv_Importer I) then
			((pre_initialization I) \<and> (
		let 
(I_initialed::Importer) = (initialization I)
		in
			(if (inv_Importer I_initialed) then
			((pre_cosimulationStep I_initialed) \<and> (
		let 
(I2::Importer) = (cosimulationStep I_initialed)
		in
			(if (inv_Importer I2) then
			(pre_terminate I2)
		 else
			undefined
		)
		))
		 else
			undefined
		)
		))
		 else
			undefined
		)
		))"


\<comment>\<open>VDM source: post_runScenario: (Scenario * Importer +> bool)
	post_runScenario(scenario, RESULT) ==
null\<close>
\<comment>\<open>in 'Clocks' (Clocks.vdmsl) at line 2000:5\<close>
definition
	post_runScenario :: "Scenario \<Rightarrow> Importer \<Rightarrow> bool"
where
	"post_runScenario scenario   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_runScenario` specification.\<close>
		(inv_Scenario scenario  \<and>  inv_Importer RESULT)"

definition
	runScenario :: "Scenario \<Rightarrow> Importer"
where
	"runScenario scenario \<equiv> 
	\<comment>\<open>User defined body of runScenario.\<close>
	(
		let 
(I::Importer) = (createImporter scenario   (10::VDMNat1)   (5::VDMNat1))
		;
		
(I_initialed::Importer) = (initialization I)
		;
		
(I2::Importer) = (cosimulationStep I_initialed)
		in
			(if (inv_Importer I)
	 \<and> 
	(inv_Importer I_initialed)
	 \<and> 
	(inv_Importer I2) then
			(terminate I2)
		 else
			undefined
		)
		)"

end