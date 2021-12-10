package plugins;

import java.util.Iterator;
import java.util.List;
import java.util.Vector;

import com.fujitsu.vdmj.lex.LexException;
import com.fujitsu.vdmj.lex.LexLocation;
import com.fujitsu.vdmj.messages.Console;
import com.fujitsu.vdmj.messages.InternalException;
import com.fujitsu.vdmj.messages.VDMErrorsException;
import com.fujitsu.vdmj.messages.VDMWarning;
import com.fujitsu.vdmj.pog.ProofObligation;
import com.fujitsu.vdmj.pog.ProofObligationList;
import com.fujitsu.vdmj.runtime.Interpreter;
import com.fujitsu.vdmj.runtime.ModuleInterpreter;
import com.fujitsu.vdmj.syntax.ParserException;
import com.fujitsu.vdmj.tc.expressions.TCExpression;
import com.fujitsu.vdmj.tc.modules.TCModuleList;
import com.fujitsu.vdmj.typechecker.TypeCheckException;

import vdm2isa.lex.IsaToken;
import vdm2isa.lex.TRIsaVDMCommentList;
import vdm2isa.messages.IsaErrorMessage;
import vdm2isa.pog.IsaProofObligationList;
import vdm2isa.tr.definitions.TRProofObligationDefinition;
import vdm2isa.tr.definitions.TRProofScriptDefinition;
import vdm2isa.tr.expressions.TRExpression;
import vdm2isa.tr.modules.TRModule;
import vdm2isa.tr.modules.TRModuleList;
import vdm2isa.tr.modules.TRProofObligationModule;
import vdm2isa.tr.types.TRType;

/**
 * VDM POs to Isabelle. Cannot be called "pog2isa" as "pog" is already a command! 
 */
public class IsapogPlugin extends GeneralisaPlugin {

    private int localPOCount;
    private IsaProofStrategy strategy;

    public IsapogPlugin(Interpreter interpreter) {
        super(interpreter);
    }

    @Override
    protected void localReset()
    {
        super.localReset();
        localPOCount = 0;
        strategy = IsaProofStrategy.SURRENDER;//IsaProofStrategy.REALISTIC;
    }

    public int getLocalPOCount()
    {
        return localPOCount;
    }

    protected void addLocalPOS(int toadd)
    {
        assert toadd >= 0;
        localPOCount += toadd;
    }

    protected TRProofScriptDefinition chooseProofScript(ProofObligation po, TRExpression poExpr)
    {
        switch (strategy)
        {
            case HOPEFUL    : return TRProofScriptDefinition.hopeful(po.location);
            case OPTIMISTIC : return TRProofScriptDefinition.optimistic(po.location);
            case PESSIMISTIC: return TRProofScriptDefinition.pessimistic(po.location);
            case REALISTIC  : return TRProofScriptDefinition.realistic(po.location);
            case SURRENDER  :
            default         : return TRProofScriptDefinition.surrender(po.location);
        }
    }

    protected String getSummaryPrefix()
    {
        return "Translated " + plural(getLocalPOCount(), "PO", "s") + 
            " with " + this.strategy.name().toLowerCase() + " proof strategy for ";
    }

    @Override
    public boolean isaRun(TCModuleList tclist, String[] argv) throws Exception {
        boolean result = false;
        if (interpreter instanceof ModuleInterpreter)
        {
            Vdm2isaPlugin vdm2isa = new Vdm2isaPlugin(interpreter);
            result = vdm2isa.run(argv);  
            if (result)
                Console.out.println("Starting Isabelle VDM Proof Obligation generation.");
            try
			{
                // create an isabelle module interpreter 
                ModuleInterpreter minterpreter = (ModuleInterpreter)interpreter;
                IsaInterpreter isaInterpreter = new IsaInterpreter(minterpreter);

                // get the POG and create a corresponding TRModuleList with its PO definitions 
                ProofObligationList pogl = isaInterpreter.getProofObligations();
                IsaProofObligationList isapogl = new IsaProofObligationList();
                int poNumber = 1;
                List<Pair<ProofObligation, Exception>> notTranslatedPOS = new Vector<Pair<ProofObligation, Exception>>();
                for(ProofObligation po : pogl)
                {
                    // do not process VDMToolkit.vdmsl POs
                    if (po.location.module.equals(IsaToken.VDMTOOLKIT.toString())) continue;

                    try 
                    {
                        // type check PO as an TC AST
                        
                        //Pair<TCExpression, TCType> pair  = isaInterpreter.typeCheck(po.value, po.location.module);
                        //TODO check pair.value is type okay; for VDM POGs should always be fine, but there will be "mine" as well ;-)

                        TCExpression potcExpr = po.getCheckedExpression();

                        // translate the PO back to TR world
                        //Pair<TRExpression, TRType> mpair = isaInterpreter.map2isa(pair);
                        TRExpression potrExpr = isaInterpreter.map2isa(potcExpr);

                        TRProofScriptDefinition poScript = chooseProofScript(po, potrExpr);
                        TRIsaVDMCommentList comments = TRIsaVDMCommentList.newComment(po.location, "VDM PO("+ poNumber +"): \"" + po.toString() + "\"", false);
                        TRType poType = null;
                        TRProofObligationDefinition poe = TRProofObligationDefinition.newProofObligationDefinition(comments, po, potrExpr, poType /* TRType for potrExpr!*/, poScript);
                        isapogl.add(poe);
                        poNumber++;
                    }
                    // added those after the problem with post_constS(,10)! for constS: ()->nat constS()==10 post RESULT <= 10;
                    // because these are "console" (not within the file) location info is mostly pointless? Except perhaps for VDMErrorsException
                    catch(LexException le)
                    {
                        // POs shouldn't fail to parse? VDMJ error?
                        GeneralisaPlugin.report(IsaErrorMessage.PO_PROCESSING_ERROR_4P, LexLocation.ANY, po.number, po.name, "lexing", le.toString());//le.location
                        notTranslatedPOS.add(new Pair<ProofObligation, Exception>(po, le));
                    }
                    catch(ParserException pe) 
                    {
                        // POs shouldn't fail to parse? VDMJ error?
                        GeneralisaPlugin.report(IsaErrorMessage.PO_PROCESSING_ERROR_4P, LexLocation.ANY, po.number, po.name, "parsing", pe.toString());//pe.location
                        notTranslatedPOS.add(new Pair<ProofObligation, Exception>(po, pe));
                    }
                    catch(TypeCheckException te)
                    {
                        // POs shouldn't fail to type check, but if they do...
                        //TODO consider any related context
                        GeneralisaPlugin.report(IsaErrorMessage.PO_PROCESSING_ERROR_4P, LexLocation.ANY, po.number, po.name, "type checking", te.toString());//te.location
                        notTranslatedPOS.add(new Pair<ProofObligation, Exception>(po, te));
                    }
                    catch(VDMErrorsException ve)
                    {
                        // POs shouldn't fail to type check, but if they do...
                        //TODO consider any related context
                        GeneralisaPlugin.report(IsaErrorMessage.PO_PROCESSING_ERROR_4P, ve.errors.isEmpty() ? LexLocation.ANY : ve.errors.get(0).location, 
                            po.number, po.name, "type checking", ve.toString());
                        notTranslatedPOS.add(new Pair<ProofObligation, Exception>(po, ve));
                    }
                    catch(Exception e)
                    {
                        // This is something quite bad, so stop
                        GeneralisaPlugin.report(IsaErrorMessage.PO_PROCESSING_ERROR_4P, LexLocation.ANY, po.number, po.name, "class mapping / unexpected", e.toString());
                        // in case we decide to comment the throw?
                        notTranslatedPOS.add(new Pair<ProofObligation, Exception>(po, e));
                        throw e;
                    }
                }
                addLocalErrors(GeneralisaPlugin.getErrorCount());

				// be strict on translation output
				// strict => AbstractIsaPlugin.getErrorCount() == 0 && getLocalErrorCount() == 0
                if (!GeneralisaPlugin.strict || (/*AbstractIsaPlugin.getErrorCount() == 0 &&*/ getLocalErrorCount() == 0))
                {
                    // output POs per module
                    TRModuleList modules = isapogl.getModulePOs();
                    addLocalModules(modules.size());
                    for (TRModule module : modules)
                    {
                        if (module instanceof TRProofObligationModule) 
                        {
                            addLocalPOS(module.definitions.size());
                            StringBuilder sb = new StringBuilder();
                            sb.append(module.translate());
                            sb.append(getUntranslatedPOSAsComments(notTranslatedPOS, (TRProofObligationModule)module));
                            outputModule(module.getLocation(), module.name.toString(), sb.toString());    
                        }
                        else
                        {
                            report(IsaErrorMessage.PO_INVALID_PO_MODULE_1P, module.name.getLocation(), module.name.toString());
                        }
                    }
                }
			}
			catch (InternalException e)
			{
				Console.out.println(e.toString());
                GeneralisaPlugin.errs++;
			}
			catch (Throwable t)
			{
				Console.out.println("Uncaught exception: " + t.toString());
				t.printStackTrace();
				GeneralisaPlugin.errs++;
			}
        }
        return result;
    }

    /**
     * Consider failed PO translation at least adding them as comments. For now at the end of the file. Later perhaps as part of
     * a proper TRIsaCommentList. 
     * @param listOfnotTranslatedPOS
     * @param module
     * @return
     */
    private String getUntranslatedPOSAsComments(List<Pair<ProofObligation, Exception>> listOfnotTranslatedPOS, TRProofObligationModule module) {
        StringBuilder sb = new StringBuilder();
        // only within the POs of the same module; remove from the list afterwards 
        Iterator<Pair<ProofObligation, Exception>> it = listOfnotTranslatedPOS.iterator();
        while (it.hasNext())
        {
            Pair<ProofObligation, Exception> pair = it.next();
            if (pair.key.location.module.equals(module.poModuleOwner))
            {
                it.remove();
                sb.append("\n");
                sb.append(IsaToken.bracketit(IsaToken.BLOCK_COMMENT_OPEN, 
                    "\n\tCould not translate VDM PO because of a " + pair.value.getClass().getSimpleName() + " error:" +
                    "\n\tVDM PO: " + pair.key.toString() + 
                    "\n\tReason: " + pair.value.getMessage() +
                    "\n", 
                    IsaToken.BLOCK_COMMENT_CLOSE));
                sb.append("\n");
            } 
        }
        return sb.toString();
    }

    @Override
    public String help() {
        return "isapog - translate VDM pog results for Isabelle/HOL (v. " + GeneralisaPlugin.isaVersion + ")";
    }

    public static void report(int number, String problem, LexLocation location)
	{
		GeneralisaPlugin.report(number, problem, location);
	}

	public static void reportAsError(VDMWarning w)
	{
		GeneralisaPlugin.reportAsError(w);
	}

	public static void warning(int number, String problem, LexLocation location)
	{
		GeneralisaPlugin.warning(number, problem, location);
	}
}
