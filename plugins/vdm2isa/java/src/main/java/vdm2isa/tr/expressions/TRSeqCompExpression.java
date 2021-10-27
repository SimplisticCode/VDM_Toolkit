package vdm2isa.tr.expressions;

import com.fujitsu.vdmj.lex.LexLocation;
import com.fujitsu.vdmj.tc.expressions.TCSeqCompExpression;
import com.fujitsu.vdmj.tc.expressions.TCSetCompExpression;

import vdm2isa.lex.IsaToken;
import vdm2isa.tr.patterns.TRMultipleBind;
import vdm2isa.tr.patterns.TRMultipleBindList;

/**
 * Isabelle sequence compression is "[ expr(bind1, bind2) . bind1 <- gen1, bind2 <- gen2, filter ]".
 * VDM sequence compression is "[ expr(bind1) . bin1 in set(q) expr2 & filter ]".
 * 
 * That is despite the fact that TCSeqCompExpression bind has a TCPatternList? In any case, we need to extract bind name 
 */
public class TRSeqCompExpression extends TRExpression {
    private static final long serialVersionUID = 1L;

    private final TRExpression first;
    private final TRMultipleBind bind;
    private final TRExpression predicate;

    public TRSeqCompExpression(LexLocation location, TRExpression first, TRMultipleBind bind, TRExpression predicate)
    {
        super(location);
        this.first = first;
        this.bind = bind;
        this.predicate = predicate;
        System.out.println("SeqComp bind = " + bind.getClass().getName() + " plist (" + bind.plist.size() + ")[" + bind.plist.get(0).isaToken().toString() + "] = " + bind.plist.toString());
    }

    @Override
    public IsaToken isaToken() {
        return IsaToken.SEQ;
    }

    @Override
    public String translate() {
        StringBuilder sb = new StringBuilder();
        sb.append(IsaToken.SEQ_OPEN.toString());
        sb.append(" ");
        sb.append(first.translate());
        sb.append(" ");
        sb.append(IsaToken.POINT.toString());
        sb.append(" ");
        sb.append(bind.translate());
        if (predicate != null)
        {
            sb.append(" ");
            sb.append("|");
            sb.append(" ");
            sb.append(predicate.translate());
        }
        sb.append(" ");
        sb.append(IsaToken.SEQ_CLOSE.toString());
        return sb.toString();
    }

}