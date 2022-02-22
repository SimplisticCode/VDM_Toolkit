(* VDM to Isabelle Translation @2022-02-22T07:29:32.569834Z
   Copyright 2021, Leo Freitas, leo.freitas@newcastle.ac.uk

in 'recordsSTH.vdmsl' at line 1:8
files = [recordsSTH.vdmsl]
*)
theory recordsSTH
imports "VDMToolkit" 
begin


\<comment>\<open>VDM source: S = compose S of x:nat, y:nat end
	inv mk_S(x, y) == (x < y)
	eq mk_S(x, y) = s1 == ((x = (s1.x)) and (y = (s1.y)))
	ord mk_S(x, y) < s1 == ((x < (s1.x)) and (y < (s1.y)))\<close>
\<comment>\<open>in 'recordsSTH' (recordsSTH.vdmsl) at line 6:5\<close>
record S = 
	x\<^sub>S :: "VDMNat"
		 
		 y\<^sub>S :: "VDMNat"
	

\<comment>\<open>VDM source: inv_S: (S +> bool)
	inv_S(mk_S(x, y)) ==
(x < y)\<close>
\<comment>\<open>in 'recordsSTH' (recordsSTH.vdmsl) at line 15:9\<close>
definition
	inv_S :: "S \<Rightarrow> bool"
where
	"inv_S dummy0 \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `inv_S` specification.\<close>
		( (((inv_VDMNat (x\<^sub>S dummy0))) \<and> 
		 ((inv_VDMNat (y\<^sub>S dummy0))) ))  \<and> 
		\<comment>\<open>Implicit pattern context conversion\<close>
		(let x = (x\<^sub>S dummy0); y = (y\<^sub>S dummy0) in 
		\<comment>\<open>User defined body of inv_S.\<close>
		(x < y))"
 

\<comment>\<open>VDM source: eq_S: (S * S +> bool)
	eq_S(mk_S(x, y), s1) ==
((x = (s1.x)) and (y = (s1.y)))\<close>
\<comment>\<open>in 'recordsSTH' (recordsSTH.vdmsl) at line 12:8\<close>
definition
	eq_S :: "S \<Rightarrow> S \<Rightarrow> bool"
where
	"eq_S dummy0   s1 \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `eq_S` specification.\<close>
		(inv_S dummy0  \<and>  inv_S s1)  \<and> 
		\<comment>\<open>Implicit pattern context conversion\<close>
		(let x = (x\<^sub>S dummy0); y = (y\<^sub>S dummy0) in 
		\<comment>\<open>User defined body of eq_S.\<close>
		((x = (x\<^sub>S s1)) \<and> (y = (y\<^sub>S s1))))"
 

\<comment>\<open>VDM source: ord_S: (S * S +> bool)
	ord_S(mk_S(x, y), s1) ==
((x < (s1.x)) and (y < (s1.y)))\<close>
\<comment>\<open>in 'recordsSTH' (recordsSTH.vdmsl) at line 9:9\<close>
definition
	ord_S :: "S \<Rightarrow> S \<Rightarrow> bool"
where
	"ord_S dummy0   s1 \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `ord_S` specification.\<close>
		(inv_S dummy0  \<and>  inv_S s1)  \<and> 
		\<comment>\<open>Implicit pattern context conversion\<close>
		(let x = (x\<^sub>S dummy0); y = (y\<^sub>S dummy0) in 
		\<comment>\<open>User defined body of ord_S.\<close>
		((x < (x\<^sub>S s1)) \<and> (y < (y\<^sub>S s1))))"
 
lemmas inv_S_defs = inv_S_def inv_VDMNat_def 


	
	
\<comment>\<open>VDM source: T = compose T of x:nat, y:nat end
	inv mk_T(x, y) == (x < y)
	eq mk_T(x1, y1) = mk_T(x2, y2) == ((x1 = x2) and (y1 = y2))
	ord mk_T(x1, y1) < mk_T(x2, y2) == ((x1 < x2) and (y1 < y2))\<close>
\<comment>\<open>in 'recordsSTH' (recordsSTH.vdmsl) at line 20:5\<close>
record T = 
	x\<^sub>T :: "VDMNat"
		 
		 y\<^sub>T :: "VDMNat"
	

\<comment>\<open>VDM source: inv_T: (T +> bool)
	inv_T(mk_T(x, y)) ==
(x < y)\<close>
\<comment>\<open>in 'recordsSTH' (recordsSTH.vdmsl) at line 29:9\<close>
definition
	inv_T :: "T \<Rightarrow> bool"
where
	"inv_T dummy0 \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `inv_T` specification.\<close>
		( (((inv_VDMNat (x\<^sub>T dummy0))) \<and> 
		 ((inv_VDMNat (y\<^sub>T dummy0))) ))  \<and> 
		\<comment>\<open>Implicit pattern context conversion\<close>
		(let x = (x\<^sub>T dummy0); y = (y\<^sub>T dummy0) in 
		\<comment>\<open>User defined body of inv_T.\<close>
		(x < y))"

		

\<comment>\<open>VDM source: eq_T: (T * T +> bool)
	eq_T(mk_T(x1, y1), mk_T(x2, y2)) ==
((x1 = x2) and (y1 = y2))\<close>
\<comment>\<open>in 'recordsSTH' (recordsSTH.vdmsl) at line 26:8\<close>
definition
	eq_T :: "T \<Rightarrow> T \<Rightarrow> bool"
where
	"eq_T dummy0   dummy0 \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `eq_T` specification.\<close>
		(inv_T dummy0  \<and>  inv_T dummy0)  \<and> 
		\<comment>\<open>Implicit pattern context conversion\<close>
		(let x1 = (x\<^sub>T dummy0); y1 = (y\<^sub>T dummy0); 
			x1 = (x\<^sub>T dummy0); y1 = (y\<^sub>T dummy0) in 
		\<comment>\<open>User defined body of eq_T.\<close>
		((x1 = x2) \<and> (y1 = y2)))"

		

\<comment>\<open>VDM source: ord_T: (T * T +> bool)
	ord_T(mk_T(x1, y1), mk_T(x2, y2)) ==
((x1 < x2) and (y1 < y2))\<close>
\<comment>\<open>in 'recordsSTH' (recordsSTH.vdmsl) at line 23:9\<close>
definition
	ord_T :: "T \<Rightarrow> T \<Rightarrow> bool"
where
	"ord_T dummy0   dummy0 \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for  `ord_T` specification.\<close>
		(inv_T dummy0  \<and>  inv_T dummy0)  \<and> 
		\<comment>\<open>Implicit pattern context conversion\<close>
		(let x1 = (x\<^sub>T dummy0); y1 = (y\<^sub>T dummy0); 
			x1 = (x\<^sub>T dummy0); y1 = (y\<^sub>T dummy0) in 
		\<comment>\<open>User defined body of ord_T.\<close>
		((x1 < x2) \<and> (y1 < y2)))"

		
lemmas inv_T_defs = inv_T_def inv_VDMNat_def 


	
	
\<comment>\<open>VDM source: transform: (S * S -> T)
	transform(mk_S(x, y), mk_S(x2, y2)) ==
mk_T((x + y2), (x2 + y))\<close>
\<comment>\<open>in 'recordsSTH' (recordsSTH.vdmsl) at line 34:3\<close>

\<comment>\<open>VDM source: pre_transform: (S * S +> bool)
	pre_transform(mk_S(x, y), mk_S(x2, y2)) ==
null\<close>
\<comment>\<open>in 'recordsSTH' (recordsSTH.vdmsl) at line 34:3\<close>
definition
	pre_transform :: "S \<Rightarrow> S \<Rightarrow> bool"
where
	"pre_transform dummy0   dummy0 \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `pre_transform` specification.\<close>
		(inv_S dummy0  \<and>  inv_S dummy0)"


\<comment>\<open>VDM source: post_transform: (S * S * T +> bool)
	post_transform(mk_S(x, y), mk_S(x2, y2), RESULT) ==
null\<close>
\<comment>\<open>in 'recordsSTH' (recordsSTH.vdmsl) at line 34:3\<close>
definition
	post_transform :: "S \<Rightarrow> S \<Rightarrow> T \<Rightarrow> bool"
where
	"post_transform dummy0   dummy0   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_transform` specification.\<close>
		(inv_S dummy0  \<and>  inv_S dummy0  \<and>  inv_T RESULT)"

definition
	transform :: "S \<Rightarrow> S \<Rightarrow> T"
where
	"transform dummy0   dummy0 \<equiv> 
	\<comment>\<open>Implicit pattern context conversion\<close>
	(let x = (x\<^sub>S dummy0); y = (y\<^sub>S dummy0); 
			x = (x\<^sub>S dummy0); y = (y\<^sub>S dummy0) in 
	\<comment>\<open>User defined body of transform.\<close>
	\<lparr>x\<^sub>T = (x + y2), y\<^sub>T = (x2 + y)\<rparr>)"

	
	
\<comment>\<open>VDM source: transform1: (S * S -> T)
	transform1(s1, s2) ==
mk_T(((s1.x) + (s2.y)), ((s2.x) + (s1.y)))\<close>
\<comment>\<open>in 'recordsSTH' (recordsSTH.vdmsl) at line 39:3\<close>

\<comment>\<open>VDM source: pre_transform1: (S * S +> bool)
	pre_transform1(s1, s2) ==
null\<close>
\<comment>\<open>in 'recordsSTH' (recordsSTH.vdmsl) at line 39:3\<close>
definition
	pre_transform1 :: "S \<Rightarrow> S \<Rightarrow> bool"
where
	"pre_transform1 s1   s2 \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `pre_transform1` specification.\<close>
		(inv_S s1  \<and>  inv_S s2)"


\<comment>\<open>VDM source: post_transform1: (S * S * T +> bool)
	post_transform1(s1, s2, RESULT) ==
null\<close>
\<comment>\<open>in 'recordsSTH' (recordsSTH.vdmsl) at line 39:3\<close>
definition
	post_transform1 :: "S \<Rightarrow> S \<Rightarrow> T \<Rightarrow> bool"
where
	"post_transform1 s1   s2   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_transform1` specification.\<close>
		(inv_S s1  \<and>  inv_S s2  \<and>  inv_T RESULT)"

definition
	transform1 :: "S \<Rightarrow> S \<Rightarrow> T"
where
	"transform1 s1   s2 \<equiv> 
	\<comment>\<open>User defined body of transform1.\<close>
	\<lparr>x\<^sub>T = ((x\<^sub>S s1) + (y\<^sub>S s2)), y\<^sub>T = ((x\<^sub>S s2) + (y\<^sub>S s1))\<rparr>"

end