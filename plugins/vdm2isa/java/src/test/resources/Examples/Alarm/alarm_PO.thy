(* VDM to Isabelle Translation @2022-02-26T09:59:26.726Z
   Copyright 2021, Leo Freitas, leo.freitas@newcastle.ac.uk

in 'alarm' (/Users/nljsf/Local/reps/git/VDM_Toolkit/plugins/vdm2isa/java/src/test/resources/Examples/Alarm/alarm.vdmsl) at line 33:7
files = [/Users/nljsf/Local/reps/git/VDM_Toolkit/plugins/vdm2isa/java/src/test/resources/Examples/Alarm/alarm.vdmsl]
*)
theory alarm_PO
imports alarm
begin


\<comment>\<open>VDM source: Expert = ?\<close>
\<comment>\<open>in 'alarm' (/Users/nljsf/Local/reps/git/VDM_Toolkit/plugins/vdm2isa/java/src/test/resources/Examples/Alarm/alarm.vdmsl) at line 33:7\<close>
theorem Expert_TOTAL_PO1:
	\<comment>\<open>Implicitly defined type invariant checks for quantified type binds\<close> 
	"((\<forall> (ex :: Expert)  . ((( ((((inv_VDMToken' (inv_VDMSeq' (inv_VDMChar)) (expertid\<^sub>E\<^sub>x\<^sub>p\<^sub>e\<^sub>r\<^sub>t ex)))) \<and> 
		 ((inv_VDMSet' ((inv_Qualification )) (quali\<^sub>E\<^sub>x\<^sub>p\<^sub>e\<^sub>r\<^sub>t ex))) ))) \<longrightarrow> isTest ((inv_Expert ex)) (inv_bool))))"
	
	oops
	
	
	
	
\<comment>\<open>VDM source: Expert = ?\<close>
\<comment>\<open>in 'alarm' (/Users/nljsf/Local/reps/git/VDM_Toolkit/plugins/vdm2isa/java/src/test/resources/Examples/Alarm/alarm.vdmsl) at line 31:3\<close>
theorem Expert_INV_SATISFIABILITY_PO2:
	\<comment>\<open>Implicitly defined type invariant checks for quantified type binds\<close> 
	"((\<exists> (ex :: Expert)  . (((
		((((inv_VDMToken' (inv_VDMSeq' (inv_VDMChar)) (expertid\<^sub>E\<^sub>x\<^sub>p\<^sub>e\<^sub>r\<^sub>t ex)))) \<and> 
		 ((inv_VDMSet' ((inv_Qualification )) (quali\<^sub>E\<^sub>x\<^sub>p\<^sub>e\<^sub>r\<^sub>t ex)))
		))) \<longrightarrow> ((quali\<^sub>E\<^sub>x\<^sub>p\<^sub>e\<^sub>r\<^sub>t ex) \<noteq> {}))))"
	
	oops
	
	
	
	
\<comment>\<open>VDM source: Schedule = ?\<close>
\<comment>\<open>in 'alarm' (/Users/nljsf/Local/reps/git/VDM_Toolkit/plugins/vdm2isa/java/src/test/resources/Examples/Alarm/alarm.vdmsl) at line 36:7\<close>
theorem Schedule_TOTAL_PO3:
	\<comment>\<open>Implicitly defined type invariant checks for quantified type binds\<close> 
	"((\<forall> (sch :: (Period \<rightharpoonup> Expert VDMSet))  . ((((inv_Map ((inv_VDMToken' (inv_VDMSeq' (inv_VDMChar)))) (inv_VDMSet' inv_Expert ) sch))) \<longrightarrow> isTest ((inv_Schedule sch)) (inv_bool))))"
	
	oops
	
	
	
	
\<comment>\<open>VDM source: Schedule = ?\<close>
\<comment>\<open>in 'alarm' (/Users/nljsf/Local/reps/git/VDM_Toolkit/plugins/vdm2isa/java/src/test/resources/Examples/Alarm/alarm.vdmsl) at line 35:3\<close>
theorem Schedule_INV_SATISFIABILITY_PO4:
	\<comment>\<open>Implicitly defined type invariant checks for quantified type binds\<close> 
	"((\<exists> (sch :: (Period \<rightharpoonup> Expert VDMSet))  . ((((inv_Map ((inv_VDMToken' (inv_VDMSeq' (inv_VDMChar)))) (inv_VDMSet' inv_Expert ) sch))) \<longrightarrow> (\<forall> exs \<in> (rng sch)  . ((exs \<noteq> {}) \<and> (\<forall> ex1 \<in> exs  . (\<forall> ex2 \<in> exs  . ((ex1 \<noteq> ex2) \<longrightarrow> ((expertid\<^sub>E\<^sub>x\<^sub>p\<^sub>e\<^sub>r\<^sub>t ex1) \<noteq> (expertid\<^sub>E\<^sub>x\<^sub>p\<^sub>e\<^sub>r\<^sub>t ex2))))))))))"
	
	oops
	
	
	
	
\<comment>\<open>VDM source: Plant = ?\<close>
\<comment>\<open>in 'alarm' (/Users/nljsf/Local/reps/git/VDM_Toolkit/plugins/vdm2isa/java/src/test/resources/Examples/Alarm/alarm.vdmsl) at line 54:7\<close>
theorem Plant_TOTAL_PO5:
	\<comment>\<open>Implicitly defined type invariant checks for quantified type binds\<close> 
	"((\<forall> (dummy0 :: Plant)  . ((( ((((inv_Map ((inv_VDMToken' (inv_VDMSeq' (inv_VDMChar)))) (inv_VDMSet' inv_Expert ) (schedule\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>t dummy0)))) \<and> 
		 ((inv_VDMSet' inv_Alarm  (alarms\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>t dummy0))) ))) \<longrightarrow> (let schedule = (schedule\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>t dummy0); alarms = (alarms\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>t dummy0) in isTest ((inv_Plant \<lparr>schedule\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>t = schedule, alarms\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>t = alarms\<rparr>)) (inv_bool)))))"
	
	oops
	
	
	
	
\<comment>\<open>VDM source: Plant = ?\<close>
\<comment>\<open>in 'alarm' (/Users/nljsf/Local/reps/git/VDM_Toolkit/plugins/vdm2isa/java/src/test/resources/Examples/Alarm/alarm.vdmsl) at line 57:26\<close>
theorem Plant_MAP_APPLY_PO6:
	\<comment>\<open>Implicitly defined type invariant checks for quantified type binds\<close> 
	"((\<forall> (dummy0 :: Plant)  . (((
		((((inv_Map ((inv_VDMToken' (inv_VDMSeq' (inv_VDMChar)))) (inv_VDMSet' inv_Expert ) (schedule\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>t dummy0)))) \<and> 
		 ((inv_VDMSet' inv_Alarm  (alarms\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>t dummy0)))
		))) \<longrightarrow> (let schedule = (schedule\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>t dummy0); alarms = (alarms\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>t dummy0) in (\<forall> a \<in> alarms  . (\<forall> peri \<in> (dom schedule)  . (peri \<in> (dom schedule))))))))"
	
	oops
	
	
	
	
\<comment>\<open>VDM source: Plant = ?\<close>
\<comment>\<open>in 'alarm' (/Users/nljsf/Local/reps/git/VDM_Toolkit/plugins/vdm2isa/java/src/test/resources/Examples/Alarm/alarm.vdmsl) at line 52:3\<close>
theorem Plant_INV_SATISFIABILITY_PO7:
	\<comment>\<open>Implicitly defined type invariant checks for quantified type binds\<close> 
	"((\<exists> (dummy0 :: Plant)  . (((
		((((inv_Map ((inv_VDMToken' (inv_VDMSeq' (inv_VDMChar)))) (inv_VDMSet' inv_Expert ) (schedule\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>t dummy0)))) \<and> 
		 ((inv_VDMSet' inv_Alarm  (alarms\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>t dummy0)))
		))) \<longrightarrow> (let schedule = (schedule\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>t dummy0); alarms = (alarms\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>t dummy0) in (\<forall> a \<in> alarms  . (\<forall> peri \<in> (dom schedule)  . (QualificationOK ((the(schedule peri)))   (quali\<^sub>A\<^sub>l\<^sub>a\<^sub>r\<^sub>m a))))))))"
	
	oops
	
	
	
	
\<comment>\<open>VDM source: NumberOfExperts = ?\<close>
\<comment>\<open>in 'alarm' (/Users/nljsf/Local/reps/git/VDM_Toolkit/plugins/vdm2isa/java/src/test/resources/Examples/Alarm/alarm.vdmsl) at line 63:10\<close>
theorem NumberOfExperts_MAP_APPLY_PO8:
	\<comment>\<open>Implicitly defined type invariant checks for quantified type binds\<close> 
	"((\<forall> (peri :: Period)   (plant :: Plant)  . (((((inv_VDMToken' (inv_VDMSeq' (inv_VDMChar)) peri))))  \<and>  ((
		((((inv_Map ((inv_VDMToken' (inv_VDMSeq' (inv_VDMChar)))) (inv_VDMSet' inv_Expert ) (schedule\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>t plant)))) \<and> 
		 ((inv_VDMSet' inv_Alarm  (alarms\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>t plant)))
		))) \<longrightarrow> ((peri \<in> (dom (schedule\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>t plant))) \<longrightarrow> (peri \<in> (dom (schedule\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>t plant)))))))"
	
	oops
	
	
	
	
\<comment>\<open>VDM source: ExpertIsOnDuty = ?\<close>
\<comment>\<open>in 'alarm' (/Users/nljsf/Local/reps/git/VDM_Toolkit/plugins/vdm2isa/java/src/test/resources/Examples/Alarm/alarm.vdmsl) at line 68:44\<close>
theorem ExpertIsOnDuty_MAP_APPLY_PO9:
	\<comment>\<open>Implicitly defined type invariant checks for quantified type binds\<close> 
	"((\<forall> (ex :: Expert)   (dummy0 :: Plant)  . (((
		((((inv_VDMToken' (inv_VDMSeq' (inv_VDMChar)) (expertid\<^sub>E\<^sub>x\<^sub>p\<^sub>e\<^sub>r\<^sub>t ex)))) \<and> 
		 ((inv_VDMSet' ((inv_Qualification )) (quali\<^sub>E\<^sub>x\<^sub>p\<^sub>e\<^sub>r\<^sub>t ex)))
		)))  \<and>  ((
		((((inv_Map ((inv_VDMToken' (inv_VDMSeq' (inv_VDMChar)))) (inv_VDMSet' inv_Expert ) (schedule\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>t dummy0)))) \<and> 
		 ((inv_VDMSet' inv_Alarm  (alarms\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>t dummy0)))
		))) \<longrightarrow> (let sch = (schedule\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>t dummy0); dollarany1 = (alarms\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>t dummy0) in (\<forall> peri \<in> (dom sch)  . (peri \<in> (dom sch)))))))"
	
	oops
	
	
	
	
\<comment>\<open>VDM source: ExpertToPage = ?\<close>
\<comment>\<open>in 'alarm' (/Users/nljsf/Local/reps/git/VDM_Toolkit/plugins/vdm2isa/java/src/test/resources/Examples/Alarm/alarm.vdmsl) at line 71:3\<close>
theorem ExpertToPage_FUNC_POST_CONDITION_PO10:
	\<comment>\<open>Implicitly defined type invariant checks for quantified type binds\<close> 
	"((\<forall> (a :: Alarm)   (peri :: Period)   (plant :: Plant)  . ((( (((inv_VDMSeq' (inv_VDMChar) (alarmtext\<^sub>A\<^sub>l\<^sub>a\<^sub>r\<^sub>m a))) \<and> 
		 ((((inv_True (quali\<^sub>A\<^sub>l\<^sub>a\<^sub>r\<^sub>m a))))) )))  \<and>  ((((inv_VDMToken' (inv_VDMSeq' (inv_VDMChar)) peri))))  \<and>  (( ((((inv_Map ((inv_VDMToken' (inv_VDMSeq' (inv_VDMChar)))) (inv_VDMSet' inv_Expert ) (schedule\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>t plant)))) \<and> 
		 ((inv_VDMSet' inv_Alarm  (alarms\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>t plant))) ))) \<longrightarrow> ((pre_ExpertToPage a   peri   plant) \<longrightarrow> (post_ExpertToPage a   peri   plant   \<lparr>expertid\<^sub>E\<^sub>x\<^sub>p\<^sub>e\<^sub>r\<^sub>t = (Token (''Leo'')), quali\<^sub>E\<^sub>x\<^sub>p\<^sub>e\<^sub>r\<^sub>t = {Qualification.U_Elec }\<rparr>)))))"
	
	oops
	
	
	
	
\<comment>\<open>VDM source: ExpertToPage = ?\<close>
\<comment>\<open>in 'alarm' (/Users/nljsf/Local/reps/git/VDM_Toolkit/plugins/vdm2isa/java/src/test/resources/Examples/Alarm/alarm.vdmsl) at line 75:22\<close>
theorem ExpertToPage_MAP_APPLY_PO11:
	\<comment>\<open>Implicitly defined type invariant checks for quantified type binds\<close> 
	"((\<forall> (a :: Alarm)   (peri :: Period)   (plant :: Plant)  . (((
		(((inv_VDMSeq' (inv_VDMChar) (alarmtext\<^sub>A\<^sub>l\<^sub>a\<^sub>r\<^sub>m a))) \<and> 
		 ((((inv_True (quali\<^sub>A\<^sub>l\<^sub>a\<^sub>r\<^sub>m a)))))
		)))  \<and>  ((((inv_VDMToken' (inv_VDMSeq' (inv_VDMChar)) peri))))  \<and>  ((
		((((inv_Map ((inv_VDMToken' (inv_VDMSeq' (inv_VDMChar)))) (inv_VDMSet' inv_Expert ) (schedule\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>t plant)))) \<and> 
		 ((inv_VDMSet' inv_Alarm  (alarms\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>t plant)))
		))) \<longrightarrow> (((peri \<in> (dom (schedule\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>t plant))) \<and> (a \<in> (alarms\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>t plant))) \<longrightarrow> (
		let 
(RESULT::Expert) = \<lparr>expertid\<^sub>E\<^sub>x\<^sub>p\<^sub>e\<^sub>r\<^sub>t = (Token (''Leo'')), quali\<^sub>E\<^sub>x\<^sub>p\<^sub>e\<^sub>r\<^sub>t = {Qualification.U_Elec }\<rparr>
		in
			(if (inv_Expert RESULT) then
			(peri \<in> (dom (schedule\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>t plant)))
		 else
			undefined
		)
		)))))"
	
	oops
	
	
	
	
\<comment>\<open>VDM source: ExpertToPage = ?\<close>
\<comment>\<open>in 'alarm' (/Users/nljsf/Local/reps/git/VDM_Toolkit/plugins/vdm2isa/java/src/test/resources/Examples/Alarm/alarm.vdmsl) at line 72:35\<close>
theorem ExpertToPage_SUB_TYPE_PO12:
	\<comment>\<open>Implicitly defined type invariant checks for quantified type binds\<close> 
	"((\<forall> (a :: Alarm)   (peri :: Period)   (plant :: Plant)  . (((
		(((inv_VDMSeq' (inv_VDMChar) (alarmtext\<^sub>A\<^sub>l\<^sub>a\<^sub>r\<^sub>m a))) \<and> 
		 ((((inv_True (quali\<^sub>A\<^sub>l\<^sub>a\<^sub>r\<^sub>m a)))))
		)))  \<and>  ((((inv_VDMToken' (inv_VDMSeq' (inv_VDMChar)) peri))))  \<and>  ((
		((((inv_Map ((inv_VDMToken' (inv_VDMSeq' (inv_VDMChar)))) (inv_VDMSet' inv_Expert ) (schedule\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>t plant)))) \<and> 
		 ((inv_VDMSet' inv_Alarm  (alarms\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>t plant)))
		))) \<longrightarrow> (((peri \<in> (dom (schedule\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>t plant))) \<and> (a \<in> (alarms\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>t plant))) \<longrightarrow> (inv_Expert \<lparr>expertid\<^sub>E\<^sub>x\<^sub>p\<^sub>e\<^sub>r\<^sub>t = (Token (''Leo'')), quali\<^sub>E\<^sub>x\<^sub>p\<^sub>e\<^sub>r\<^sub>t = {Qualification.U_Elec }\<rparr>)))))"
	
	oops
	
	
	
	
\<comment>\<open>VDM source: ChangeExpert = ?\<close>
\<comment>\<open>in 'alarm' (/Users/nljsf/Local/reps/git/VDM_Toolkit/plugins/vdm2isa/java/src/test/resources/Examples/Alarm/alarm.vdmsl) at line 81:30\<close>
theorem ChangeExpert_MAP_APPLY_PO13:
	\<comment>\<open>Implicitly defined type invariant checks for quantified type binds\<close> 
	"((\<forall> (dummy0 :: Plant)   (v11 :: Expert)   (v22 :: Expert)   (peri :: Period)  . (((
		((((inv_Map ((inv_VDMToken' (inv_VDMSeq' (inv_VDMChar)))) (inv_VDMSet' inv_Expert ) (schedule\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>t dummy0)))) \<and> 
		 ((inv_VDMSet' inv_Alarm  (alarms\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>t dummy0)))
		)))  \<and>  ((
		((((inv_VDMToken' (inv_VDMSeq' (inv_VDMChar)) (expertid\<^sub>E\<^sub>x\<^sub>p\<^sub>e\<^sub>r\<^sub>t v11)))) \<and> 
		 ((inv_VDMSet' ((inv_Qualification )) (quali\<^sub>E\<^sub>x\<^sub>p\<^sub>e\<^sub>r\<^sub>t v11)))
		)))  \<and>  ((
		((((inv_VDMToken' (inv_VDMSeq' (inv_VDMChar)) (expertid\<^sub>E\<^sub>x\<^sub>p\<^sub>e\<^sub>r\<^sub>t v22)))) \<and> 
		 ((inv_VDMSet' ((inv_Qualification )) (quali\<^sub>E\<^sub>x\<^sub>p\<^sub>e\<^sub>r\<^sub>t v22)))
		)))  \<and>  ((((inv_VDMToken' (inv_VDMSeq' (inv_VDMChar)) peri)))) \<longrightarrow> (let plan = (schedule\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>t dummy0); alarms = (alarms\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>t dummy0) in  (peri \<in> (dom plan))))))"
	
	oops
	
	
	
	
\<comment>\<open>VDM source: ChangeExpert = ?\<close>
\<comment>\<open>in 'alarm' (/Users/nljsf/Local/reps/git/VDM_Toolkit/plugins/vdm2isa/java/src/test/resources/Examples/Alarm/alarm.vdmsl) at line 81:17\<close>
theorem ChangeExpert_SUB_TYPE_PO14:
	\<comment>\<open>Implicitly defined type invariant checks for quantified type binds\<close> 
	"((\<forall> (dummy0 :: Plant)   (v11 :: Expert)   (v22 :: Expert)   (peri :: Period)  . (((
		((((inv_Map ((inv_VDMToken' (inv_VDMSeq' (inv_VDMChar)))) (inv_VDMSet' inv_Expert ) (schedule\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>t dummy0)))) \<and> 
		 ((inv_VDMSet' inv_Alarm  (alarms\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>t dummy0)))
		)))  \<and>  ((
		((((inv_VDMToken' (inv_VDMSeq' (inv_VDMChar)) (expertid\<^sub>E\<^sub>x\<^sub>p\<^sub>e\<^sub>r\<^sub>t v11)))) \<and> 
		 ((inv_VDMSet' ((inv_Qualification )) (quali\<^sub>E\<^sub>x\<^sub>p\<^sub>e\<^sub>r\<^sub>t v11)))
		)))  \<and>  ((
		((((inv_VDMToken' (inv_VDMSeq' (inv_VDMChar)) (expertid\<^sub>E\<^sub>x\<^sub>p\<^sub>e\<^sub>r\<^sub>t v22)))) \<and> 
		 ((inv_VDMSet' ((inv_Qualification )) (quali\<^sub>E\<^sub>x\<^sub>p\<^sub>e\<^sub>r\<^sub>t v22)))
		)))  \<and>  ((((inv_VDMToken' (inv_VDMSeq' (inv_VDMChar)) peri)))) \<longrightarrow> (let plan = (schedule\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>t dummy0); alarms = (alarms\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>t dummy0) in  ((inv_Schedule (plan \<dagger> [peri\<mapsto>((((the(plan peri))) - {v11}) \<union> {v22})])) \<and> isTest ((plan \<dagger> [peri\<mapsto>((((the(plan peri))) - {v11}) \<union> {v22})])) (inv_Map ((inv_VDMToken' (inv_VDMSeq' (inv_VDMChar)))) (inv_VDMSet' inv_Expert )))))))"
	
	oops
	
	
	
	
\<comment>\<open>VDM source: ChangeExpert = ?\<close>
\<comment>\<open>in 'alarm' (/Users/nljsf/Local/reps/git/VDM_Toolkit/plugins/vdm2isa/java/src/test/resources/Examples/Alarm/alarm.vdmsl) at line 81:3\<close>
theorem ChangeExpert_SUB_TYPE_PO15:
	\<comment>\<open>Implicitly defined type invariant checks for quantified type binds\<close> 
	"((\<forall> (dummy0 :: Plant)   (v11 :: Expert)   (v22 :: Expert)   (peri :: Period)  . ((( ((((inv_Map ((inv_VDMToken' (inv_VDMSeq' (inv_VDMChar)))) (inv_VDMSet' inv_Expert ) (schedule\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>t dummy0)))) \<and> 
		 ((inv_VDMSet' inv_Alarm  (alarms\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>t dummy0))) )))  \<and>  ((
		((((inv_VDMToken' (inv_VDMSeq' (inv_VDMChar)) (expertid\<^sub>E\<^sub>x\<^sub>p\<^sub>e\<^sub>r\<^sub>t v11)))) \<and> 
		 ((inv_VDMSet' ((inv_Qualification )) (quali\<^sub>E\<^sub>x\<^sub>p\<^sub>e\<^sub>r\<^sub>t v11)))
		)))  \<and>  ((
		((((inv_VDMToken' (inv_VDMSeq' (inv_VDMChar)) (expertid\<^sub>E\<^sub>x\<^sub>p\<^sub>e\<^sub>r\<^sub>t v22)))) \<and> 
		 ((inv_VDMSet' ((inv_Qualification )) (quali\<^sub>E\<^sub>x\<^sub>p\<^sub>e\<^sub>r\<^sub>t v22)))
		)))  \<and>  ((((inv_VDMToken' (inv_VDMSeq' (inv_VDMChar)) peri)))) \<longrightarrow> (let plan = (schedule\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>t dummy0); alarms = (alarms\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>t dummy0) in  ((inv_Plant \<lparr>schedule\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>t = (plan \<dagger> [peri\<mapsto>((((the(plan peri))) - {v11}) \<union> {v22})]), alarms\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>t = alarms\<rparr>) \<and> ((inv_Schedule (plan \<dagger> [peri\<mapsto>((((the(plan peri))) - {v11}) \<union> {v22})])) \<and> isTest ((plan \<dagger> [peri\<mapsto>((((the(plan peri))) - {v11}) \<union> {v22})])) (inv_Map ((inv_VDMToken' (inv_VDMSeq' (inv_VDMChar)))) (inv_VDMSet' inv_Expert ))))))))"
	
	oops
	
	
	
	
\<comment>\<open>VDM source: e1 = ?\<close>
\<comment>\<open>in 'alarm' (/Users/nljsf/Local/reps/git/VDM_Toolkit/plugins/vdm2isa/java/src/test/resources/Examples/Alarm/alarm.vdmsl) at line 101:15\<close>
theorem e1_SUB_TYPE_PO16:
	"((inv_Expert \<lparr>expertid\<^sub>E\<^sub>x\<^sub>p\<^sub>e\<^sub>r\<^sub>t = eid1, quali\<^sub>E\<^sub>x\<^sub>p\<^sub>e\<^sub>r\<^sub>t = {Qualification.U_Elec }\<rparr>))"
	
	oops
	
	
	
	
\<comment>\<open>VDM source: e2 = ?\<close>
\<comment>\<open>in 'alarm' (/Users/nljsf/Local/reps/git/VDM_Toolkit/plugins/vdm2isa/java/src/test/resources/Examples/Alarm/alarm.vdmsl) at line 102:15\<close>
theorem e2_SUB_TYPE_PO17:
	"((inv_Expert \<lparr>expertid\<^sub>E\<^sub>x\<^sub>p\<^sub>e\<^sub>r\<^sub>t = eid2, quali\<^sub>E\<^sub>x\<^sub>p\<^sub>e\<^sub>r\<^sub>t = {Qualification.U_Mech  , Qualification.U_Chem }\<rparr>))"
	
	oops
	
	
	
	
\<comment>\<open>VDM source: e3 = ?\<close>
\<comment>\<open>in 'alarm' (/Users/nljsf/Local/reps/git/VDM_Toolkit/plugins/vdm2isa/java/src/test/resources/Examples/Alarm/alarm.vdmsl) at line 103:15\<close>
theorem e3_SUB_TYPE_PO18:
	"((inv_Expert \<lparr>expertid\<^sub>E\<^sub>x\<^sub>p\<^sub>e\<^sub>r\<^sub>t = eid3, quali\<^sub>E\<^sub>x\<^sub>p\<^sub>e\<^sub>r\<^sub>t = {Qualification.U_Bio  , Qualification.U_Chem  , Qualification.U_Elec }\<rparr>))"
	
	oops
	
	
	
	
\<comment>\<open>VDM source: e4 = ?\<close>
\<comment>\<open>in 'alarm' (/Users/nljsf/Local/reps/git/VDM_Toolkit/plugins/vdm2isa/java/src/test/resources/Examples/Alarm/alarm.vdmsl) at line 104:15\<close>
theorem e4_SUB_TYPE_PO19:
	"((inv_Expert \<lparr>expertid\<^sub>E\<^sub>x\<^sub>p\<^sub>e\<^sub>r\<^sub>t = eid4, quali\<^sub>E\<^sub>x\<^sub>p\<^sub>e\<^sub>r\<^sub>t = {Qualification.U_Bio }\<rparr>))"
	
	oops
	
	
	
	
\<comment>\<open>VDM source: e5 = ?\<close>
\<comment>\<open>in 'alarm' (/Users/nljsf/Local/reps/git/VDM_Toolkit/plugins/vdm2isa/java/src/test/resources/Examples/Alarm/alarm.vdmsl) at line 105:15\<close>
theorem e5_SUB_TYPE_PO20:
	"((inv_Expert \<lparr>expertid\<^sub>E\<^sub>x\<^sub>p\<^sub>e\<^sub>r\<^sub>t = eid5, quali\<^sub>E\<^sub>x\<^sub>p\<^sub>e\<^sub>r\<^sub>t = {Qualification.U_Chem  , Qualification.U_Bio }\<rparr>))"
	
	oops
	
	
	
	
\<comment>\<open>VDM source: e6 = ?\<close>
\<comment>\<open>in 'alarm' (/Users/nljsf/Local/reps/git/VDM_Toolkit/plugins/vdm2isa/java/src/test/resources/Examples/Alarm/alarm.vdmsl) at line 106:15\<close>
theorem e6_SUB_TYPE_PO21:
	"((inv_Expert \<lparr>expertid\<^sub>E\<^sub>x\<^sub>p\<^sub>e\<^sub>r\<^sub>t = eid6, quali\<^sub>E\<^sub>x\<^sub>p\<^sub>e\<^sub>r\<^sub>t = {Qualification.U_Elec  , Qualification.U_Chem  , Qualification.U_Bio  , Qualification.U_Mech }\<rparr>))"
	
	oops
	
	
	
	
\<comment>\<open>VDM source: e7 = ?\<close>
\<comment>\<open>in 'alarm' (/Users/nljsf/Local/reps/git/VDM_Toolkit/plugins/vdm2isa/java/src/test/resources/Examples/Alarm/alarm.vdmsl) at line 107:15\<close>
theorem e7_SUB_TYPE_PO22:
	"((inv_Expert \<lparr>expertid\<^sub>E\<^sub>x\<^sub>p\<^sub>e\<^sub>r\<^sub>t = eid7, quali\<^sub>E\<^sub>x\<^sub>p\<^sub>e\<^sub>r\<^sub>t = {Qualification.U_Elec  , Qualification.U_Mech }\<rparr>))"
	
	oops
	
	
	
	
\<comment>\<open>VDM source: e8 = ?\<close>
\<comment>\<open>in 'alarm' (/Users/nljsf/Local/reps/git/VDM_Toolkit/plugins/vdm2isa/java/src/test/resources/Examples/Alarm/alarm.vdmsl) at line 108:15\<close>
theorem e8_SUB_TYPE_PO23:
	"((inv_Expert \<lparr>expertid\<^sub>E\<^sub>x\<^sub>p\<^sub>e\<^sub>r\<^sub>t = eid8, quali\<^sub>E\<^sub>x\<^sub>p\<^sub>e\<^sub>r\<^sub>t = {Qualification.U_Mech  , Qualification.U_Bio }\<rparr>))"
	
	oops
	
	
	
	
\<comment>\<open>VDM source: s = ?\<close>
\<comment>\<open>in 'alarm' (/Users/nljsf/Local/reps/git/VDM_Toolkit/plugins/vdm2isa/java/src/test/resources/Examples/Alarm/alarm.vdmsl) at line 112:8\<close>
theorem s_MAP_SEQ_OF_COMPATIBLE_PO24:
	"((\<forall> m1 \<in> {[p1\<mapsto>{e7 , e5 , e1}] , [p2\<mapsto>{e6}] , [p3\<mapsto>{e1 , e3 , e8}] , [p4\<mapsto>{e6}]}  . (\<forall> m2 \<in> {[p1\<mapsto>{e7 , e5 , e1}] , [p2\<mapsto>{e6}] , [p3\<mapsto>{e1 , e3 , e8}] , [p4\<mapsto>{e6}]}  . (\<forall> d3 \<in> (dom m1)  . (\<forall> d4 \<in> (dom m2)  . ((d3 = d4) \<longrightarrow> ((m1 d3) = (m2 d4))))))))"
	
	oops
	
	
	
	
\<comment>\<open>VDM source: plant1 = ?\<close>
\<comment>\<open>in 'alarm' (/Users/nljsf/Local/reps/git/VDM_Toolkit/plugins/vdm2isa/java/src/test/resources/Examples/Alarm/alarm.vdmsl) at line 123:29\<close>
theorem plant1_SUB_TYPE_PO25:
	"(((inv_Schedule s) \<and> isTest (s) (inv_Map ((inv_VDMToken' (inv_VDMSeq' (inv_VDMChar)))) (inv_VDMSet' inv_Expert ))))"
	
	oops
	
	
	
	
\<comment>\<open>VDM source: plant1 = ?\<close>
\<comment>\<open>in 'alarm' (/Users/nljsf/Local/reps/git/VDM_Toolkit/plugins/vdm2isa/java/src/test/resources/Examples/Alarm/alarm.vdmsl) at line 123:20\<close>
theorem plant1_SUB_TYPE_PO26:
	"(((inv_Plant \<lparr>schedule\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>t = s, alarms\<^sub>P\<^sub>l\<^sub>a\<^sub>n\<^sub>t = {a1 , a2 , a3}\<rparr>) \<and> ((inv_Schedule s) \<and> isTest (s) (inv_Map ((inv_VDMToken' (inv_VDMSeq' (inv_VDMChar)))) (inv_VDMSet' inv_Expert )))))"
	
	oops
	
	
\<comment>\<open>Processing VDM exports as Isabelle hidden declarations\<close>

end