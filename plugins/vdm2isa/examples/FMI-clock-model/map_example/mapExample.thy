(* VDM to Isabelle Translation @2022-02-22T07:35:56.114727Z
   Copyright 2021, Leo Freitas, leo.freitas@newcastle.ac.uk

in 'mapExample.vdmsl' at line 1:8
files = [mapExample.vdmsl]
*)
theory mapExample
imports "VDMToolkit" 
begin


\<comment>\<open>VDM source: S = compose S of x:nat end\<close>
\<comment>\<open>in 'mapExample' (mapExample.vdmsl) at line 6:5\<close>
record S = 
	x\<^sub>S :: "VDMNat"
	

\<comment>\<open>VDM source: inv_S: (S +> bool)
	inv_S(dummy0) ==
null\<close>
\<comment>\<open>in 'mapExample' (mapExample.vdmsl) at line 6:5\<close>
definition
	inv_S :: "S \<Rightarrow> bool"
where
	"inv_S dummy0 \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `inv_S` specification.\<close>
		( (((inv_VDMNat (x\<^sub>S dummy0))) ))"
 
lemmas inv_S_defs = inv_S_def inv_VDMNat_def 


	
	
\<comment>\<open>VDM source: T = compose T of y:map (nat) to (S) end\<close>
\<comment>\<open>in 'mapExample' (mapExample.vdmsl) at line 9:5\<close>
record T = 
	y\<^sub>T :: "(VDMNat \<rightharpoonup> S)"
	

\<comment>\<open>VDM source: inv_T: (T +> bool)
	inv_T(dummy0) ==
null\<close>
\<comment>\<open>in 'mapExample' (mapExample.vdmsl) at line 9:5\<close>
definition
	inv_T :: "T \<Rightarrow> bool"
where
	"inv_T dummy0 \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `inv_T` specification.\<close>
		( (((inv_Map (inv_VDMNat) inv_S  (y\<^sub>T dummy0))) ))"
 
lemmas inv_T_defs = inv_Map_def inv_Map_defs inv_S_def inv_T_def inv_VDMNat_def 


	
	
\<comment>\<open>VDM source: f: (T * S -> nat)
	f(m, s) ==
((m.y)(((m.y)((s.x)).x)).x)\<close>
\<comment>\<open>in 'mapExample' (mapExample.vdmsl) at line 14:5\<close>

\<comment>\<open>VDM source: pre_f: (T * S +> bool)
	pre_f(m, s) ==
null\<close>
\<comment>\<open>in 'mapExample' (mapExample.vdmsl) at line 14:5\<close>
definition
	pre_f :: "T \<Rightarrow> S \<Rightarrow> bool"
where
	"pre_f m   s \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `pre_f` specification.\<close>
		(inv_T m  \<and>  inv_S s)"


\<comment>\<open>VDM source: post_f: (T * S * nat +> bool)
	post_f(m, s, RESULT) ==
null\<close>
\<comment>\<open>in 'mapExample' (mapExample.vdmsl) at line 14:5\<close>
definition
	post_f :: "T \<Rightarrow> S \<Rightarrow> VDMNat \<Rightarrow> bool"
where
	"post_f m   s   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_f` specification.\<close>
		(inv_T m  \<and>  inv_S s  \<and>  (inv_VDMNat RESULT))"

definition
	f :: "T \<Rightarrow> S \<Rightarrow> VDMNat"
where
	"f m   s \<equiv> 
	\<comment>\<open>User defined body of f.\<close>
	(x\<^sub>S (the(((y\<^sub>T m) (x\<^sub>S (the(((y\<^sub>T m) (x\<^sub>S s)))))))))"

	
	
\<comment>\<open>VDM source: g: (T * S -> nat)
	g(m, s) ==
f(m, (m.y)(((m.y)((s.x)).x)))\<close>
\<comment>\<open>in 'mapExample' (mapExample.vdmsl) at line 19:5\<close>

\<comment>\<open>VDM source: pre_g: (T * S +> bool)
	pre_g(m, s) ==
null\<close>
\<comment>\<open>in 'mapExample' (mapExample.vdmsl) at line 19:5\<close>
definition
	pre_g :: "T \<Rightarrow> S \<Rightarrow> bool"
where
	"pre_g m   s \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `pre_g` specification.\<close>
		(inv_T m  \<and>  inv_S s)"


\<comment>\<open>VDM source: post_g: (T * S * nat +> bool)
	post_g(m, s, RESULT) ==
null\<close>
\<comment>\<open>in 'mapExample' (mapExample.vdmsl) at line 19:5\<close>
definition
	post_g :: "T \<Rightarrow> S \<Rightarrow> VDMNat \<Rightarrow> bool"
where
	"post_g m   s   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_g` specification.\<close>
		(inv_T m  \<and>  inv_S s  \<and>  (inv_VDMNat RESULT))"

definition
	g :: "T \<Rightarrow> S \<Rightarrow> VDMNat"
where
	"g m   s \<equiv> 
	\<comment>\<open>User defined body of g.\<close>
	(f m   ((y\<^sub>T m) (x\<^sub>S (the(((y\<^sub>T m) (x\<^sub>S s)))))))"

	
	
\<comment>\<open>VDM source: h: (S * S -> S)
	h(mk_S(x), mk_S(y)) ==
mk_S((x + y))\<close>
\<comment>\<open>in 'mapExample' (mapExample.vdmsl) at line 23:5\<close>

\<comment>\<open>VDM source: pre_h: (S * S +> bool)
	pre_h(mk_S(x), mk_S(y)) ==
null\<close>
\<comment>\<open>in 'mapExample' (mapExample.vdmsl) at line 23:5\<close>
definition
	pre_h :: "S \<Rightarrow> S \<Rightarrow> bool"
where
	"pre_h dummy0   dummy0 \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `pre_h` specification.\<close>
		(inv_S dummy0  \<and>  inv_S dummy0)"


\<comment>\<open>VDM source: post_h: (S * S * S +> bool)
	post_h(mk_S(x), mk_S(y), RESULT) ==
null\<close>
\<comment>\<open>in 'mapExample' (mapExample.vdmsl) at line 23:5\<close>
definition
	post_h :: "S \<Rightarrow> S \<Rightarrow> S \<Rightarrow> bool"
where
	"post_h dummy0   dummy0   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_h` specification.\<close>
		(inv_S dummy0  \<and>  inv_S dummy0  \<and>  inv_S RESULT)"

definition
	h :: "S \<Rightarrow> S \<Rightarrow> S"
where
	"h dummy0   dummy0 \<equiv> 
	\<comment>\<open>Implicit pattern context conversion\<close>
	(let x = (x\<^sub>S dummy0); 
			x = (x\<^sub>S dummy0) in 
	\<comment>\<open>User defined body of h.\<close>
	\<lparr>x\<^sub>S = (x + y)\<rparr>)"

	
	
\<comment>\<open>VDM source: h': (S * S -> S)
	h'(a, b) ==
let mk_S(x):S = a, mk_S(y):S = b in mk_S((x + y))\<close>
\<comment>\<open>in 'mapExample' (mapExample.vdmsl) at line 26:5\<close>

\<comment>\<open>VDM source: pre_h': (S * S +> bool)
	pre_h'(a, b) ==
null\<close>
\<comment>\<open>in 'mapExample' (mapExample.vdmsl) at line 26:5\<close>
definition
	pre_h' :: "S \<Rightarrow> S \<Rightarrow> bool"
where
	"pre_h' a   b \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `pre_h'` specification.\<close>
		(inv_S a  \<and>  inv_S b)"


\<comment>\<open>VDM source: post_h': (S * S * S +> bool)
	post_h'(a, b, RESULT) ==
null\<close>
\<comment>\<open>in 'mapExample' (mapExample.vdmsl) at line 26:5\<close>
definition
	post_h' :: "S \<Rightarrow> S \<Rightarrow> S \<Rightarrow> bool"
where
	"post_h' a   b   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_h'` specification.\<close>
		(inv_S a  \<and>  inv_S b  \<and>  inv_S RESULT)"

definition
	h' :: "S \<Rightarrow> S \<Rightarrow> S"
where
	"h' a   b \<equiv> 
	\<comment>\<open>User defined body of h'.\<close>
	(
		let 
(dummy0::S) = a
		;
		
(dummy0::S) = b
		in
			let x = (x\<^sub>S dummy0) in 
		let y = (x\<^sub>S dummy0) in (if (inv_S dummy0)
	 \<and> 
	(inv_S dummy0) then
			\<lparr>x\<^sub>S = (x + y)\<rparr>
		 else
			undefined
		)
		)"

	
	
\<comment>\<open>VDM source: h'': (S * S -> S)
	h''(a, b) ==
mk_S(((a.x) + (b.x)))\<close>
\<comment>\<open>in 'mapExample' (mapExample.vdmsl) at line 31:5\<close>

\<comment>\<open>VDM source: pre_h'': (S * S +> bool)
	pre_h''(a, b) ==
null\<close>
\<comment>\<open>in 'mapExample' (mapExample.vdmsl) at line 31:5\<close>
definition
	pre_h'' :: "S \<Rightarrow> S \<Rightarrow> bool"
where
	"pre_h'' a   b \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `pre_h''` specification.\<close>
		(inv_S a  \<and>  inv_S b)"


\<comment>\<open>VDM source: post_h'': (S * S * S +> bool)
	post_h''(a, b, RESULT) ==
null\<close>
\<comment>\<open>in 'mapExample' (mapExample.vdmsl) at line 31:5\<close>
definition
	post_h'' :: "S \<Rightarrow> S \<Rightarrow> S \<Rightarrow> bool"
where
	"post_h'' a   b   RESULT \<equiv> 
		\<comment>\<open>Implicitly defined type invariant checks for undeclared `post_h''` specification.\<close>
		(inv_S a  \<and>  inv_S b  \<and>  inv_S RESULT)"

definition
	h'' :: "S \<Rightarrow> S \<Rightarrow> S"
where
	"h'' a   b \<equiv> 
	\<comment>\<open>User defined body of h''.\<close>
	\<lparr>x\<^sub>S = ((x\<^sub>S a) + (x\<^sub>S b))\<rparr>"

end