package vdm2isa.tr.patterns;

import vdm2isa.lex.IsaToken;
import vdm2isa.tr.types.TRType;

public class TRMultipleTypeBind extends TRMultipleBind {
    
    private static final long serialVersionUID = 1L;

    private final TRType type;
    private final String separator;

    public TRMultipleTypeBind(TRPattern pattern, TRType type)
    {
        this(pattern.getPatternList(), type);
    }

    public TRMultipleTypeBind(TRPatternList plist, TRType type)
    {
        super(plist);
        this.type = type;
        this.separator = " ";
    }

    @Override
    public IsaToken isaToken() {
        return IsaToken.INSET;
    }

    protected String invTranslate(int index)
    {
        assert index >= 0 && index < plist.size();
        return IsaToken.parenthesise(IsaToken.INV + type.translate() + " " + plist.get(index).translate());
    }

    public String invTranslate()
    {
        StringBuilder sb = new StringBuilder();
		if (!plist.isEmpty())
		{
			sb.append(invTranslate(0));
            for (int i=1; i<plist.size(); i++)
			{
                sb.append(" " + IsaToken.AND.toString() + " ");
				sb.append(invTranslate(i));
			}
		}
		return sb.toString();
    }

    protected String translate(int index, String typeStr)
    {
        assert index >= 0 && index < plist.size();
        return IsaToken.parenthesise(plist.get(index).translate() + typeStr);
    }

    @Override
    public String translate() {
        StringBuilder sb = new StringBuilder();
		if (!plist.isEmpty())
		{
            // translate each item with it's type case, e.g. "(x::VDMNat)"
            String typeStr = IsaToken.TYPEOF.toString() + type.translate();
			sb.append(translate(0, typeStr));

            for (int i=1; i<plist.size(); i++)
			{
                //TODO doesn't this need a separator? Like " "?
                sb.append(separator);
				sb.append(translate(i, typeStr));
			}
		}
		return sb.toString();
    }
}