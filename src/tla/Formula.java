package tla;

import java.util.List;
import java.util.ArrayList;
import java.util.Set;
import java.util.HashSet;

/**
 * class Formula - represents a definition in TLA+ of the form LHS == RHS
 */
public class Formula {
    protected String LHS;
    protected List<String> RHS;
    // Variables that are changed by this formula
    protected Set<String> changed; 
    // Variables that are unchanged by this formula
    protected Set<String> unchanged;
    // Program counter before and after this operation
    protected int pc = 0;
    protected int pcAfter = 0;
    // The separator used to join components of the right hand side (e.g. /\ or \/)
    protected String separator;
    // Used to flag the formula as corresponding to a break statement, used so that
    // we don't make the post pc be the beginning of the loop if there happens to be
    // a break right at the end of the loop
    protected boolean isBreakStatement;
    // Used to flag an empty loop for special cases of pc after the condition
    protected boolean isEmptyLoop;
    // Exec component corresponding to this formula/concrete operation, if applicable
    protected Formula exec = null;
    
    public Formula( String LHS ) {
        this.LHS = LHS;
        this.RHS = new ArrayList<String>();
        this.changed = new HashSet<String>();
        this.unchanged = new HashSet<String>();
        this.separator = "/\\";
        changed.add("pc");
        isBreakStatement = false;
        isEmptyLoop = false;
    }
    public int getPc() {
        return pc;
    }
    public int getPostPc() {
        return pcAfter;
    }
    public void setPc(int pc) {
        this.pc = pc;
    }
    public boolean isBreakStatement() {
        return isBreakStatement;
    }
    public void flagAsBreakStatement() {
        this.isBreakStatement = true;
    }
    public boolean isEmptyLoop() {
        return isEmptyLoop;
    }
    public void flagAsEmptyLoop() {
        this.isEmptyLoop = true;
    }
    public void setSeparator(String separator) {
        this.separator = separator;
    }
    public Set<String> getChanged() {
        return changed;
    }
    public Set<String> getUnchanged() {
        return unchanged;
    }
    public String getLHS() {
        return LHS;
    }
    public List<String> getRHS() {
        return RHS;
    }
    public void addRHS(String s) {
        if(s == null) return;
        RHS.add(s);
    }
    public void constrainPc(int before, int after) {
        pc = before;
        pcAfter = after;
    }
    public void addChanged(String s) {
        changed.add(s);
    }
    public void addUnchanged(String s) {
        unchanged.add(s);
    }
    public void setExec(Formula exec) {
        this.exec = exec;
    }
    public Formula getExec() {
        return this.exec;
    }
    /*
     * Print LHS == RHS
     */
    public String printLine() {
        String result = new String();
        result += LHS;
        result += " == ";
        result += printRHS();
        return result;
    }
    /*
     * Print only the right hand side of the formula
     */
    public String printRHS() {
        // New list of logic elements with program counter constraints at front
        List<String> orderedRHS = new ArrayList<String>();
        // If we haven't constrained pc, it is just some generic logic, don't need to see pc
        if(pc != 0 || pcAfter != 0) {
            orderedRHS.add("pc = " + pc);
            orderedRHS.add("pc' = " + pcAfter);
        }
        orderedRHS.addAll(RHS);
        RHS = orderedRHS;
        String result = new String();
        if(LHS.equals("Init")) {
            result += separator;
        }
        for(String item: RHS) {
            result += " " + item + " ";
            result += separator;
        }
        if(result.endsWith(separator)) result = result.substring(0, result.length()-separator.length());
        return result;
    }
    
    /*
     * Remove the last component of the RHS, used for purposes of re-ordering
     */
    public String removeLast() {
        String result = "";
        if(RHS.size() > 0) {
            result = RHS.remove(RHS.size() - 1);
        }
        return result;
    }
}