package vdm2isa.tr.patterns;

import vdm2isa.lex.IsaToken;
import vdm2isa.tr.TRNode;
import vdm2isa.tr.expressions.TRExpression;
import vdm2isa.tr.patterns.visitors.TRMultipleBindVisitor;

/**
 * VDM set binds represent "x in set S". Depending on the translation context, different outcomes are needed.
 * For typing or parameters context, that is just "x : S"; whereas for comprehension contexts, it depends on
 * whether this bind is for a set or seq comprehenion, in which case certain transformations are needed.
 */
public class TRMultipleSetBind extends TRMultipleBind 
{
    private static final long serialVersionUID = 1L;

    private final TRExpression set;

    // TRSeqComp sets this to true for the case [ x | x in set S ], where S is ordered
    public boolean seqBind;

    public TRMultipleSetBind(TRPattern pattern, TRExpression set)
    {
        this(pattern.getPatternList(), set);
    }

    public TRMultipleSetBind(TRPatternList plist, TRExpression set)
    {
        super(plist);
        this.set = set;
        // If this set bind is part of a sequence bind or not; to be set by the TRSeqCompExpression
        this.seqBind = false;
    }

    @Override
    public IsaToken isaToken() {
        return IsaToken.INSET;
    }

    /**
     * Set bindings translation in comprehension just needs the name, given the actual bind will be in the 
     * predicate part (see TRSetCompExpression). If this bind is for a sequence comprehension, Isabelle 
     * requires the set to be ordered and to be translated to a sequence. Given VDM enforces set ordering 
     * as well, a call to "sorted_set_as_list" is issued through IsaToken.SETSEQBIND under the right circumstances.
     * Pattern only parameter is for when the bind is used in the generator field, rather than predicate field.  
     */
    @Override
    public String compTranslate(boolean vdmPatternsOnly)
    {
        StringBuilder sb = new StringBuilder();
        sb.append(plist.translate());
        // for seq comprehension with ordered seq bind, we need the extra SETSEQBIND mapping
        // whenever it's not just for the patterns, which should never be the case any how.  
        if (!vdmPatternsOnly && seqBind)
        { 
            // On type checked VDM values the underlying type is ordered; but possibly with an ord_ clause, which might not work for Isabelle 
            String setbindProblem = "Set bind \"" + translate() + "\" in sequence comprehension requires VDM set to be ordered (i.e. its Isabelle type instantiates type class linorder).";
            warning(11111, setbindProblem);
            sb.append(getFormattingSeparator());
            sb.append(IsaToken.SETSEQBIND);
            sb.append(getFormattingSeparator());
            sb.append(IsaToken.parenthesise(set.translate()));
        }
        return sb.toString();
    }
    
    @Override
    public String translate() {
        StringBuilder sb = new StringBuilder();
		if (plist.isEmpty())
        {   //TODO is this even possible? 
            report(11111, "Invalid empty set bind pattern.");
        }
        else
		{
            String setStr = set.translate();
			sb.append(plist.get(0).translate());
			sb.append(getFormattingSeparator());
			sb.append(isaToken().toString());
	        sb.append(getFormattingSeparator());
			sb.append(setStr);
    		for (int i = 1; i < plist.size(); i++)
			{
				sb.append(getSemanticSeparator());
				sb.append(getFormattingSeparator());
				sb.append(plist.get(i).translate());
                sb.append(getFormattingSeparator());
				sb.append(isaToken().toString());
				sb.append(getFormattingSeparator());
				sb.append(setStr);
			}
		}
		return sb.toString();
    }

    /**
     * Allow invTranslate calls for MultipleSeq bind, given it only contains one pattern;
     * in the context where they are within a mixed type and set/seq binds! 
     * 
     * For set binds, translate each individual pattern like translate above. (i.e. )
     */
    @Override
    public String invTranslate()
    {
        StringBuilder sb = new StringBuilder();
		if (plist.isEmpty())
        {   //TODO is this even possible? 
            report(11111, "Invalid empty set bind pattern.");
        }
        else
		{
            String setStr = set.translate();
			sb.append(plist.get(0).invTranslate());
			sb.append(getFormattingSeparator());
			sb.append(isaToken().toString());
	        sb.append(getFormattingSeparator());
			sb.append(setStr);
    		for (int i = 1; i < plist.size(); i++)
			{
				sb.append(getInvTranslateSeparator());
				sb.append(getFormattingSeparator());
				sb.append(plist.get(i).invTranslate());
				sb.append(isaToken().toString());
				sb.append(getFormattingSeparator());
				sb.append(setStr);
			}
		}
		return sb.toString();
    }

    @Override
    public TRNode getRHS() {
        return set;
    }

	@Override
	public <R, S> R apply(TRMultipleBindVisitor<R, S> visitor, S arg)
	{
		return visitor.caseMultipleSetBind(this, arg);
	}
}
