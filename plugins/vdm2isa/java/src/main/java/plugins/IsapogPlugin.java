package plugins;

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
import com.fujitsu.vdmj.tc.types.TCType;
import com.fujitsu.vdmj.typechecker.TypeCheckException;

import vdm2isa.lex.TRIsaCommentList;
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
public class IsapogPlugin extends AbstractIsaPlugin {

    private int localPOCount;

    public IsapogPlugin(Interpreter interpreter) {
        super(interpreter);
    }

    @Override
    protected void localReset()
    {
        super.localReset();
        localPOCount = 0;
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
        return TRProofScriptDefinition.optimistic(po.location);
    }

    protected String getSummaryPrefix()
    {
        return "Translated POs for ";
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
                for(ProofObligation po : pogl)
                {
                    try 
                    {
                        // type check PO as an TC AST
                        Pair<TCExpression, TCType> pair  = isaInterpreter.typeCheck(po.value, po.location.module);
                        //TODO check pair.value is type okay; for VDM POGs should always be fine, but there will be "mine" as well ;-)

                        // translate the PO back to TR world
                        Pair<TRExpression, TRType> mpair = isaInterpreter.map2isa(pair);
                        TRProofScriptDefinition poScript = chooseProofScript(po, mpair.key);
                        TRIsaCommentList comments = TRIsaCommentList.newComment(po.location, "VDM po: " + po.toString(), false);
                        TRProofObligationDefinition poe = new TRProofObligationDefinition(comments, po, mpair.key, mpair.value, poScript);
                        isapogl.add(poe);
                    }
                    // added those after the problem with post_constS(,10)! for constS: ()->nat constS()==10 post RESULT <= 10;
                    // because these are "console" (not within the file) location info is mostly pointless? Except perhaps for VDMErrorsException
                    catch(LexException le)
                    {
                        // POs shouldn't fail to parse? VDMJ error?
                        AbstractIsaPlugin.report(11111, "VDM PO lexing error \"" + le.toString() + "\"; should never happen, carrying on...", LexLocation.ANY);//le.location                        
                    }
                    catch(ParserException pe) 
                    {
                        // POs shouldn't fail to parse? VDMJ error?
                        AbstractIsaPlugin.report(11111, "VDM PO parsing error \"" + pe.toString() + "\"; should never happen, carrying on...", LexLocation.ANY);//pe.location);
                    }
                    catch(TypeCheckException te)
                    {
                        // POs shouldn't fail to type check, but if they do...
                        //TODO consider any related context
                        AbstractIsaPlugin.report(11111, "VDM PO type checking error \"" + te.toString() + "\"; carrying on...", LexLocation.ANY);//te.location);
                    }
                    catch(VDMErrorsException ve)
                    {
                        // POs shouldn't fail to type check, but if they do...
                        //TODO consider any related context
                        AbstractIsaPlugin.report(11111, "VDM PO type checking error \"" + ve.toString() + "\"; carrying on...", 
                            ve.errors.isEmpty() ? LexLocation.ANY : ve.errors.get(0).location);                        
                    }
                    catch(Exception e)
                    {
                        // This is something quite bad, so stop
                        AbstractIsaPlugin.report(11111, "VDM PO class mapping / unexpected error \"" + e.toString() + "\"; cannot carry on.", LexLocation.ANY);                        
                        throw e;
                    }
                }
                //TODO hum... addLocalErrors(AbstractIsaPlugin.getErrorCount());

				// be strict on translation output
				// strict => AbstractIsaPlugin.getErrorCount() == 0 && getLocalErrorCount() == 0
                if (!AbstractIsaPlugin.strict || (AbstractIsaPlugin.getErrorCount() == 0 && getLocalErrorCount() == 0))
                {
                    // output POs per module
                    TRModuleList modules = isapogl.getModulePOs();
                    addLocalModules(modules.size());
                    for (TRModule module : modules)
                    {
                        if (module instanceof TRProofObligationModule) 
                        {
                            addLocalPOS(module.definitions.size());
                            outputModule(module.getLocation(), module.name.toString(), module.translate());    
                        }
                        else
                        {
                            report(11111, "Invalid proof obligations module " + module.name.toString(), module.name.getLocation());
                        }
                    }
                }
			}
			catch (InternalException e)
			{
				Console.out.println(e.toString());
			}
			catch (Throwable t)
			{
				Console.out.println("Uncaught exception: " + t.toString());
				t.printStackTrace();
				AbstractIsaPlugin.errs++;
			}
        }
        return result;
    }

    @Override
    public String help() {
        return "isapog - translate VDM pog results for Isabelle/HOL (v. " + AbstractIsaPlugin.isaVersion + ")";
    }

    public static void report(int number, String problem, LexLocation location)
	{
		AbstractIsaPlugin.report(number, problem, location);
	}

	public static void reportAsError(VDMWarning w)
	{
		AbstractIsaPlugin.reportAsError(w);
	}

	public static void warning(int number, String problem, LexLocation location)
	{
		AbstractIsaPlugin.warning(number, problem, location);
	}
}
