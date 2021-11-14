/*******************************************************************************
 *	Copyright (c) 2020 Leo Freitas.
 ******************************************************************************/

package vdm2isa.tr.definitions;

import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.ListIterator;
import java.util.Set;
import java.util.Vector;

import com.fujitsu.vdmj.tc.annotations.TCAnnotationList;
import com.fujitsu.vdmj.tc.lex.TCNameList;
import com.fujitsu.vdmj.tc.lex.TCNameToken;
import com.fujitsu.vdmj.typechecker.NameScope;

import plugins.GeneralisaPlugin;
import plugins.Vdm2isaPlugin;
import vdm2isa.lex.IsaTemplates;
import vdm2isa.lex.IsaToken;
import vdm2isa.lex.TRIsaVDMCommentList;
import vdm2isa.messages.IsaErrorMessage;
import vdm2isa.messages.IsaWarningMessage;
import vdm2isa.tr.definitions.visitors.TRDefinitionVisitor;
import vdm2isa.tr.expressions.TRExpression;
import vdm2isa.tr.patterns.TRBasicPattern;
import vdm2isa.tr.patterns.TRPatternListList;
import vdm2isa.tr.types.TRFunctionType;
import vdm2isa.tr.types.TRType;

public class TRExplicitFunctionDefinition extends TRDefinition
{
	private static final long serialVersionUID = 1L;

	/**
	 * Only pre/post/inv can be implicitly generated when the user doesn't explicitly define them
	 * yet we must check the related (sub-)type invariants. Equality is added also because of 
	 * VDM record equality abstraction (":-"), which will require an implicit definition in Isabelle
	 * about record equality.   
	 */
	//TODO should this be extended to other bits? Probably not! 
	private static final Set<TRSpecificationKind> 
		VALID_IMPLICITLY_GENERATED_SPEC_KIND = new HashSet<TRSpecificationKind>( 
			Arrays.asList(TRSpecificationKind.PRE, 
						TRSpecificationKind.POST, 
						TRSpecificationKind.INV, 
						TRSpecificationKind.EQ));

	//private final TCNameToken name;
	private final TCNameList typeParams;
	private final TRFunctionType type;
	private final TRPatternListList parameters;
	private final TRExpression body;
	private final TRExpression precondition;
	private final TRExpression postcondition;
	private final boolean isTypeInvariant;
	private final TRExpression measureExp;
	private final boolean isCurried;
	private final boolean recursive;
	private final boolean isUndefined;
	private final TRSpecificationKind implicitSpecificationKind;
	private TRExplicitFunctionDefinition predef;
	private TRExplicitFunctionDefinition postdef;
	private final TRDefinitionListList paramDefinitionList;

	public TRExplicitFunctionDefinition(
			TRIsaVDMCommentList comments,
			TCAnnotationList annotations,
			TCNameToken name,
			NameScope nameScope, 
			boolean used, 
			boolean excluded,
			TCNameList typeParams, 
			TRFunctionType type,
			TRPatternListList parameters, 
			TRExpression body,
			TRExpression precondition,
			TRExpression postcondition, 
			boolean typeInvariant, 
			TRExpression measureExp,
			boolean isCurried, 
			TRExplicitFunctionDefinition predef,
			TRExplicitFunctionDefinition postdef,
			TRDefinitionListList paramDefinitionList,
			boolean recursive,
			boolean isUndefined)
	{	
		super(name.getLocation(), comments, annotations, name, nameScope, used, excluded);
		this.typeParams = typeParams;
		this.type = type;
		this.parameters = parameters;
		// null body for case where user does not define the pre/post explicitly but we need its TRDefinition for implicit invariant type checks?
		this.body = body;
		this.precondition = precondition;
		this.postcondition = postcondition;
		this.isTypeInvariant = typeInvariant;
		this.measureExp = measureExp;
		this.isCurried = isCurried;
		this.predef = predef;
		this.postdef = postdef;
		this.paramDefinitionList = paramDefinitionList;
		this.recursive = recursive;
		this.isUndefined = isUndefined;
		this.local = false; // LetDefExpression to set this to true if/when needed
		this.implicitSpecificationKind = impliSpecificationDefinition();

		assert this.type != null && this.name != null && this.parameters != null; 

		setup();
		// if (implicitSpecificationKind in {PRE,POST,NONE} => local) then print (i.e. no top-level print please)
		if (!Arrays.asList(
				TRSpecificationKind.PRE 
				,TRSpecificationKind.POST
				,TRSpecificationKind.NONE
				,TRSpecificationKind.INV
				,TRSpecificationKind.EQ
				,TRSpecificationKind.ORD
				,TRSpecificationKind.MAX
				,TRSpecificationKind.MIN
			).contains(implicitSpecificationKind)
			|| local
			) 
			System.out.println(toString());
    }

	@Override
	protected void setup()
	{
		if (this.type == null)
			// not fully class mapped do nothing
			super.setup();
		else
		{
			// don't call super.setup(); as we won't have the various input params yet then!
			setFormattingSeparator("\n\t\t");
			// parameters and type parameters are curried not "," separated
			//this.typeParams.setSemanticSeparator(" ");
			this.parameters.setSemanticSeparator(" ");
			
			// check stuff is consistent to expectations
			if ((precondition != null && predef == null) || (precondition == null && predef != null))
				report(IsaErrorMessage.VDMSL_INVALID_SPECIFICATION_1P, "precondition");
			if ((postcondition != null && postdef == null) || (postcondition == null && postdef != null))
				report(IsaErrorMessage.VDMSL_INVALID_SPECIFICATION_1P, "postcondition");
			
			// if the body is null, this is an implicitly generated TRExplicitFunctionDefinition,
			// which *must* be of a specific specification kind.
			if (isImplicitlyGeneratedUndeclaredSpecification() && 
				!VALID_IMPLICITLY_GENERATED_SPEC_KIND.contains(implicitSpecificationKind))
			{
				report(IsaErrorMessage.ISA_INVALID_IMPLSPEC_2P, name.toString(),
					VALID_IMPLICITLY_GENERATED_SPEC_KIND.toString());
			}

			// only create undeclared specification for those who need it: when precondition/predef are null but
			// have body that's the case (f: nat -> nat f(x) == x; no pre/post); which will then create it, but that
			// in itself won't have pre/predef and no body! So if not guarded here, would loop! 
			if (!isImplicitlyGeneratedUndeclaredSpecification() && !isSpecificationDefinition())
			{
				// user defined pre/posts will have TRExplicitFunctionDefinitions with precondition==null and prefef==null and body !=null!
				if (this.precondition == null && this.predef == null)
					this.predef = TRExplicitFunctionDefinition.createUndeclaredSpecification(name, nameScope, used, excluded, typeParams,
						type, isCurried, parameters, paramDefinitionList, TRSpecificationKind.PRE); 
				if (postcondition == null && postcondition == null)
					this.postdef = TRExplicitFunctionDefinition.createUndeclaredSpecification(name, nameScope, used, excluded, typeParams,
					type, isCurried, parameters, paramDefinitionList, TRSpecificationKind.POST); 
			}
		}
	} 

	@Override
	public String toString()
	{
		return "TRExplicitFuncDef for " + 
			" \n\tname        = " + String.valueOf(name) +
			" \n\tlocal	      = " + local + 
			" \n\tused	      = " + used + 
			" \n\texcluded    = " + excluded + 
			" \n\tnamescope	  = " + (nameScope != null ? nameScope.name() : "?") +
			" \n\tkind	      = " + implicitSpecificationKind +
			" \n\ttype params = " + String.valueOf(typeParams) + 
			" \n\ttype sig    = " + String.valueOf(type) + //(type != null ? type.translate() : "null") + 
			" \n\ttype sig in = " + (type != null ? String.valueOf(type.parameters)//.translate() + " [" + type.parameters.size() + "]" 
													: "null") +
			" \n\ttype sig out= " + String.valueOf(type) + //(type != null ? type.result.translate() : "null") +
			" \n\tparameters  = " + String.valueOf(parameters) + //(parameters != null ? parameters.toString() : null)+ 
			" \n\tbody        = " + String.valueOf(body) + // (body != null ? body.translate() : "null") + 
			" \n\tpre         = " + (precondition  != null ? precondition.getClass().getSimpleName()  + ": " + precondition.toString()  : "null") + 
			" \n\tpost        = " + (postcondition != null ? postcondition.getClass().getSimpleName() + ": " + postcondition.toString() : "null") + 
			" \n\tisTypeInv   = " + isTypeInvariant +
			" \n\tmeasure     = " + (measureExp != null ? measureExp.getClass().getSimpleName() + ": " + measureExp.toString() : "null") +
			" \n\tisCurried   = " + isCurried +
			// avoid calling translate for TLD as it creates a record of what has been translated!  
			" \n\tpredef      = " + (predef  != null ? predef.getClass().getSimpleName()  + ": \n\t========\n\t" + predef.toString() + "\n\t========\n\t"/*predef.translate()*/  : "null") +
			" \n\tpostdef     = " + (postdef != null ? postdef.getClass().getSimpleName() + ": \n\t========\n\t" + postdef.toString() + "\n\t========\n\t"/*postdef.translate()*/ : "null") +
			" \n\tparamDefList= " + (paramDefinitionList != null ? paramDefinitionList.toString() : "") +//paramDefinitionList.getFlatDefinitionList().toString() : "null") +
			" \n\trecursive   = " + recursive +
			" \n\tisUndefined = " + isUndefined +
			" \n\tsynthetic   = " + isImplicitlyGeneratedUndeclaredSpecification() +
			" \n\tin		  = " + location.toString();
	
		// f: nat -> nat
		// f(x) == x + 1;
		//
		// TRExplicitFuncDef for f 
		// 	type params = null 
		// 	type        = VDMNat \<Rightarrow> VDMNat 
		// 	parameters  = [x] 
		// 	body        = (x + (1::VDMNat1)) 
		// 	pre         = null 
		// 	post        = null 
		// 	isTypeInv   = false 
		// 	measure     = null 
		// 	isCurried   = false 
		// 	predef      = null 
		// 	postdef     = null 
		// 	paramDefList= [x = nat]
	}

	protected static TRFunctionType createUndeclaredSpecificationFunctionType(TRFunctionType type, boolean isCurried, TRSpecificationKind kind)
	{
		TRFunctionType result = null;
		switch (kind)
		{
			case PRE:
				result = type.getCurriedPreType(isCurried);
				break;
			case POST:
				result = type.getCurriedPostType(isCurried);
				break;

			case INV:
				result = type.getInvariantType();
				break;

			case ORD:
			case EQ:
			case MAX:
			case MIN:
				result = type.getComparisonType();
				break;

			case MEASURE:
				result = type.getMeasureType();
				break;

			case INIT:
			case NONE:
			default:
				type.report(IsaErrorMessage.PLUGIN_NYI_2P, "undeclared specification function type", kind);
				result = type.getUnknownType();
		}
		assert result != null;
		return result;
	}

	protected static TRPatternListList createUndeclaredSpecificationParameters(TCNameToken name, TRPatternListList parameters, TRSpecificationKind kind)
	{
		TRPatternListList result = parameters.copy();
		if (kind == TRSpecificationKind.POST)
		{
			// add synthetic RESULT extra parameter to the last patternList
			// e.g., uncurried(x,y)== x + y, will lead to [[x,y]] then [[x,y,RESULT]]
			// 		 curried(x)(y) == x + y, will lead to [[x],[y]] then [[x],[y,RESULT]]
			result.lastElement().add(
				TRBasicPattern.identifier(
						parameters.getLocation(), 
						name.getResultName(parameters.getLocation()).toString()
				)
			);
		}
		return result;
	}

	/**
	 * Constructs corresponding definition for TRExplicitFunction of interest at the same location as this function definition. 
	 * @param kind
	 */
	protected static TRExplicitFunctionDefinition createUndeclaredSpecification(
		TCNameToken name, NameScope nameScope, boolean used, boolean excluded, TCNameList typeParams, 
		TRFunctionType type, boolean isCurried, TRPatternListList parameters, 
		TRDefinitionListList paramDefinitionList, TRSpecificationKind kind)
	{
		TCNameToken undeclaredName = null;
		switch (kind)
		{
			case PRE:
				//assert owner.predef == null && owner.precondition == null;
				undeclaredName = name.getPreName(name.getLocation());
				break;
			case POST:
				//assert owner.postdef == null && owner.postcondition == null;
				undeclaredName = name.getPostName(name.getLocation());
				break;			
			case INV:
				undeclaredName = name.getInvName(name.getLocation());
				break;
	    	case EQ:
				undeclaredName = name.getEqName(name.getLocation());
				break;
			case ORD:
				undeclaredName = name.getOrdName(name.getLocation());
				break;
			case MAX:
				undeclaredName = name.getMaxName(name.getLocation());
				break;
			case MIN:
				undeclaredName = name.getMinName(name.getLocation());
				break;
			case MEASURE:
				undeclaredName = name.getMeasureName(name.getLocation());
				break;
			case INIT:
				undeclaredName = name.getInitName(name.getLocation());
				break;
			case NONE:
				undeclaredName = name; 
				GeneralisaPlugin.report(IsaErrorMessage.ISA_INVALID_IMPLSPEC_2P, name.getLocation(), name.toString(), 
					VALID_IMPLICITLY_GENERATED_SPEC_KIND.toString());
				break;
			default:
				undeclaredName = name; 
				GeneralisaPlugin.report(IsaErrorMessage.PLUGIN_NYI_2P, name.getLocation(), 
					"implicit definition for missing specification " + kind.name(), name.toString());
				break;
		}
		assert undeclaredName != null;
		TRIsaVDMCommentList comments = null;//TRIsaCommentList.newComment(location, "implicitly constructed " + kind + " specification", false);
		
		// Now create the undeclared specification as an explicit function without body (i.e. no user defined stuff).
		// The translator will then take this into account as the "missing" (now found) specification definition, and
		// treat it as if the user has given it (e.g. equivalent to as if the user had typed "pre true", "post true");  
		TRExplicitFunctionDefinition result = new TRExplicitFunctionDefinition(
					comments,										//  LexCommentList comments,								
					null,											// 	TCAnnotationList annotations,
					undeclaredName,									// 	TCNameToken name,
					nameScope, used, excluded,						//  extra TRDefinition parameters, 
					typeParams,										// 	TCNameList typeParams, 
					TRExplicitFunctionDefinition.createUndeclaredSpecificationFunctionType(type, isCurried, kind),// 	TRFunctionType type,
					TRExplicitFunctionDefinition.createUndeclaredSpecificationParameters(name, parameters, kind),	// 	TRPatternListList parameters, 
					null,											// 	TRExpression body,
					null,											// 	TRExpression precondition,
					null,											// 	TRExpression postcondition, 
					false,											// 	boolean typeInvariant, 
					null, 											// 	TRExpression measureExp,
					isCurried,								// 	boolean isCurried, 
					null,											// 	TRExplicitFunctionDefinition predef,
					null,											// 	TRExplicitFunctionDefinition postdef,
					paramDefinitionList,						// 	TRDefinitionListList paramDefinitionList,
					false,											// 	boolean recursive,
					false 											// 	boolean isUndefined
					);
		return result;
	} 
	
	/**
	 * Determines wether this TRExplicitFunctionDefinition is one of those constructed by the typechecker.
	 * Depending on which kind (if any), then translation has to take into account different considerations. 
	 * Decision is based on VDM naming conventions (e.g., pre_, post_, inv_, ord_, eq_, etc.).
	 * @return the kind of implicit specification associated with this definition
	 */
	private TRSpecificationKind impliSpecificationDefinition()
	{
		TRSpecificationKind result = TRSpecificationKind.NONE;

		// presumes Settings.release = VDM_10 and dialect = VDMSL. This is checked by GeneralisaPlugin.run anyhow
		if (name.isReserved())
		{
			String fcnName = name.getName();
			if (fcnName.startsWith("pre_")) 
				result = TRSpecificationKind.PRE;
			else if (fcnName.startsWith("post_"))
				result = TRSpecificationKind.POST;
			else if (fcnName.startsWith("inv_"))
				result = TRSpecificationKind.INV;
			else if (fcnName.startsWith("init_"))
				result = TRSpecificationKind.INIT;
			else if (fcnName.startsWith("measure_"))
				result = TRSpecificationKind.MEASURE;
			else if (fcnName.startsWith("eq_"))
				result = TRSpecificationKind.EQ;
			else if (fcnName.startsWith("ord_"))
				result = TRSpecificationKind.ORD;
			else if (fcnName.startsWith("min_"))
				result = TRSpecificationKind.MIN;
			else if (fcnName.startsWith("max_"))	
				result = TRSpecificationKind.MAX;
		}
		return result;
	} 

	/**
	 * VDM constant functions (e.g., f:() -> nat) are translated as Isabelle constants.  
	 * @return if this is a constant function
	 */
	protected boolean isConstantFunction()
	{
		return type.parameters.isEmpty();
	}

	/**
	 * For situations where the user does not define pre/posts, like in 
	 * 		f: nat -> nat
	 * 		f(x) == x;
	 * We still have to translate a pre/post_f calls to check type invariants. 
	 * Implicitily generated pre/post TRExplicitFunctionDefinition *must* have null body and pre/post/inv names!
	 *  
	 * @return true when pre/post are being implicitly generated
	 */
	protected boolean isImplicitlyGeneratedUndeclaredSpecification()
	{
		return body == null;
	}

	/**
	 * If inferred specification kind is not NONE, it means this is a TRExplicitFunctionDeclaration for either
	 * user defined specification (e.g., pre/post etc.) or implicitly generated undeclared specification 
	 * (e.g., missing pre/post checks on input types etc.). Testing this is important to avoid looping (e.g. pre_post_pre_f).
	 * @return
	 */
	protected boolean isSpecificationDefinition()
	{
		return implicitSpecificationKind != TRSpecificationKind.NONE;
	}

	private String paramsInvTranslate(TRSpecificationKind kind)
	{
		StringBuilder paramsStr = new StringBuilder();
		if (isCurried)
		{
			// if curried there are more names than parameters on the first entry
			if (type.result instanceof TRFunctionType)
			{
				assert !parameters.isEmpty();

				// get the curried parameters
				List<List<String>> curriedVarNames = parameters.varNameTranslate();
				ListIterator<List<String>> iter = curriedVarNames.listIterator();

				// translate the outmost parameters first
				List<String> varNames = iter.next();
				paramsStr.append(type.parameters.invTranslate(varNames));
				// get the innermost parameters next
				TRType next = type.result;
				while (next instanceof TRFunctionType && iter.hasNext())
				{
					// copy it for the case where we have to remove RESULT; remove RESULT from parameters as it will be treated in the next.result 
					varNames = new Vector<String>(iter.next());
					if (kind == TRSpecificationKind.POST)
					{
						String resultName = name.getResultName(location).toString();
						boolean removed = varNames.remove(resultName);
						if (!removed)
						{
							warning(IsaWarningMessage.VDMSL_MISSING_RESULT_IN_POST_1P, resultName);
						}
					}
					paramsStr.append(type.parameters.getFormattingSeparator());
					paramsStr.append(type.parameters.getInvTranslateSeparator());
					paramsStr.append(((TRFunctionType)next).parameters.invTranslate(varNames));
					next = ((TRFunctionType)next).result;
				}

				if (kind == TRSpecificationKind.POST && Vdm2isaPlugin.linientPost)
				{
					warning(IsaWarningMessage.PLUGIN_NYI_2P, "linient post condition for curried definitions", name.toString());
				}
			} 
			else
			{
				// should never happen for a type checked VDM?
				report(IsaErrorMessage.VDMSL_INVALID_CURRIED_FCNTYPE_2P, this.name.toString(), this.type.result.getClass().getSimpleName());
			}
		}
		else
		{
			// if not curried flat list and translate
			List<String> varNames = parameters.flatVarNameTranslate();

			// for TRNamedType for records, we need to adjust the inner call to the inv_R of original record,
			// rather than explicitly redefining inv_R! Fix type.parameters in TRTypeDEfinition.
			paramsStr.append(type.parameters.invTranslate(varNames));

			if (kind == TRSpecificationKind.POST && Vdm2isaPlugin.linientPost)
			{
				// include "pre_f x =>" within post (i.e. ignore RESULT from varNames) 
				assert name.getName().startsWith("post_");
				String preCall = "pre_" + name.getName().substring("post_".length()) + " ";
				String resultName = name.getResultName(location).toString();
				boolean removed = varNames.remove(resultName);
				if (!removed)
				{
					warning(IsaWarningMessage.VDMSL_MISSING_RESULTVAR_1P, resultName);
				}
				// transform "[x,y]" into "x y", "[x]" into "x", "[]" into ""
				String varList = varNames.toString().replace(',', ' ');
				assert varList.length() >= 2;
				paramsStr = new StringBuilder(IsaToken.parenthesise(
						preCall + varList.substring(1, varList.length()-1) + " " +
						IsaToken.IMPLIES.toString() + " " + // getFormattingSeparator() +
						paramsStr.toString()));
				//TODO this will possibly create "messy" formatting if separator includes \n! 
			}
		}
		return paramsStr.toString();
	}

	/**
	 * Implicit checks for pre/post. They are similar with minor differences, so parameterised here to avoid repetition
	 * at possibly the cost of making it slightly harder to follow. 
	 * @param kind
	 * @return
	 */
	//TODO should/could this be pushed to say TRType tree for the implicitly defined checks belonging there? Would be more elegant,
	//	   but would demand an extra TRExplicitFunctionDefinition? Hum... Not sure.
	protected String translateImplicitChecks(TRSpecificationKind kind)
	{
		StringBuilder fcnBody = new StringBuilder();
		
		// constant function without explicit pre gets just True
		if (kind == TRSpecificationKind.PRE && isConstantFunction() && isImplicitlyGeneratedUndeclaredSpecification())
		{
			// undeclared pre of constant functions get "True" 
			fcnBody.append(IsaToken.TRUE.toString());
		}	
		else if (VALID_IMPLICITLY_GENERATED_SPEC_KIND.contains(kind))
		{
			String implicitComment = "Implicitly defined type invariant checks for " +
				(isImplicitlyGeneratedUndeclaredSpecification() ? "undeclared " : "")+ 
				// No need to append the kind, given it will be as part of its own definition?
				/*kind.toString().toLowerCase() + */ name.toString() + " specification";

			// pre/post checks on input (including RESULT for post) types
			// there is no need to check type.result type because for PRE/POST defs that's always bool! 
			fcnBody.append(getFormattingSeparator());
			fcnBody.append(IsaToken.comment(implicitComment, getFormattingSeparator()));
			
			// translate the parameters taking currying into account!
			//String old = type.parameters.setFormattingSeparator(getFormattingSeparator()); //uncomment if want to see differently "shaped" output
			String paramsStr = paramsInvTranslate(kind);
			//type.parameters.setFormattingSeparator(old);
			fcnBody.append(paramsStr);

			// System.out.println("Implicit translation with: " + 
			// 	"\n\t params = " + parameters.getFlatPatternList().size() + 
			// 	"\n\t types  = " + type.parameters.size() +
			// 	"\n\t vars   = " + varNames.toString() +
			// 	"\n\t" + toString());

			// if there is a user defined body, add the missing conjunction for it, so long as not pre of constant function! 
			if (!isConstantFunction() && !isImplicitlyGeneratedUndeclaredSpecification())
			{
				// " \<and>"
				fcnBody.append(type.parameters.getFormattingSeparator());
				fcnBody.append(type.parameters.getInvTranslateSeparator());
			}
		}
		return fcnBody.toString();
	}

	/**
	 * Add any top-level isa comment that inner expressions might want, if we have an explicitly defined body. 
	 */
	@Override
    public String tldIsaComment()
    {
        return body != null ? tldIsaCommentTranslate(body) : super.tldIsaComment();
    }

	@Override
	public String translate()
	{
		StringBuilder sb = new StringBuilder();
		
		// add any comments and annotations
		sb.append(super.translate());
		
		// translate the precondition
		if (predef != null) 
		{
			sb.append(predef.translate());
			sb.append("\n");
		}

		// translate the postcondition
		if (postdef != null)
		{
			sb.append(postdef.translate());
			sb.append("\n");
		}

		// translate the explicit function definition taking into consideration TRSpecificationKind
		// constant functions are translated as constant definitions (not abbreviations) with null inType string.		
		String fcnName     = name.getName();
		//TODO STOPPED HERE; requires thought for TRNamedTypes in parameters! 
		String fcnInType   = isConstantFunction() ? null : type.parameters.translate();
		String fcnOutType  = type.result.translate();
		String fcnParams   = parameters.translate();
		StringBuilder fcnBody = new StringBuilder();
		switch (implicitSpecificationKind)
		{
			// ready; do nothing else
			case NONE:
				break;

			// include implicit function parameters invariant checks
			case PRE:
			case POST:
			case INV:
			case EQ:
			case ORD:
				fcnBody.append(translateImplicitChecks(implicitSpecificationKind));	
				break;

			case MAX:
			case MIN:
			case MEASURE:
				// no implicit checks, given these return non-boolean results!
				break;
			case INIT:
				break;			
		}
		String old = getFormattingSeparator();
		// include any record patterns within a single let definition for all of them
		// e.g. f(mk_R(x,y), mk_R(z,w)) == e becomes 
		//		let x = (x\<^sub>R dummy0); y = (y\<^sub>R dummy0); z = (x\<^sub>R dummy1); w = (y\<^sub>R dummy1) in e  
		if (parameters.hasRecordPatternParameters())
		{
			fcnBody.append(getFormattingSeparator());
			fcnBody.append(IsaToken.comment("Implicit record pattern projection conversion", getFormattingSeparator()));
			setFormattingSeparator("\n\t\t\t");
			fcnBody.append(parameters.recordPatternTranslate());
		}

		// implicitly generated undeclared specifications have no body
		if (!isImplicitlyGeneratedUndeclaredSpecification())
		{
			// include the user declared body after including implicit considerations
			fcnBody.append(getFormattingSeparator());
			fcnBody.append(IsaToken.comment("User defined body of " + name.toString(), getFormattingSeparator()));
			fcnBody.append(tldIsaComment());
			fcnBody.append(body.translate());
		}
		
		// translate definition according to discovered (possibly implicit) considerations. fcnInType is null for constant functions
		sb.append(IsaTemplates.translateDefinition(this.getLocation(), fcnName, fcnInType, fcnOutType, fcnParams, fcnBody.toString(), local));

		setFormattingSeparator(old);

		return sb.toString();
	}

	@Override
	public String setFormattingSeparator(String sep)
	{
		// if (getFormattingSeparator() != null && sep != null && getFormattingSeparator().equals("\n\t\t") && !sep.equals("\n\t\t"))
		// {
		// 	Throwable t = new Throwable(); 
		// 	System.out.println("Change format sep from " + getFormattingSeparator().length() + getFormattingSeparator() + " to " + sep.length() + sep); 
		// 	t.printStackTrace();
		// }
		return super.setFormattingSeparator(sep);
	}

	@Override
	public IsaToken isaToken() {
		return IsaToken.FUN;
	}

	@Override
	public <R, S> R apply(TRDefinitionVisitor<R, S> visitor, S arg)
	{
		return visitor.caseExplicitFunctionDefinition(this, arg);
	}

	public TRPatternListList getParameters()
	{
		return parameters;
	}

	public TRFunctionType getType()
	{
		return type;
	}

	public TRExpression getBody()
	{
		return body;
	}

	public TRExplicitFunctionDefinition getPredef()
	{
		return predef;
	}

	public TRExplicitFunctionDefinition getPostdef()
	{
		return postdef;
	}

	public TRExplicitFunctionDefinition getMeasureDef()
	{
		return null;	// TODO!!
	}
}
