package tree;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import source.Position;
import syms.SymEntry;
import tla.Module;

/** 
 * class StatementNode - Abstract syntax tree representation of statements. 
 * @version $Revision: 22 $  $Date: 2014-05-20 15:14:36 +1000 (Tue, 20 May 2014) $
 * Classes defined within StatementNode extend it.
 * All statements have a position within the original source code.
 */
public abstract class StatementNode {
    /** Position in the input source program */
    private Position pos;
    /** Abstract program counter */
    protected int pc;

    /** Constructor */
    protected StatementNode( Position pos, int pc) {
        this.pos = pos;
        this.pc = pc;
    }
    public Position getPosition() {
        return pos;
    }
    public int getPc() {
        return pc;
    }
    public void setPc(int pc) {
        this.pc = pc;
    }
    /** All statement nodes provide an accept method to implement the visitor
     * pattern to traverse the tree.
     * @param visitor class implementing the details of the particular
     *  traversal.
     */
    public abstract void accept( StatementVisitor visitor );
    /** All statement nodes provide a genCode method to implement the visitor
     * pattern to traverse the tree for code generation.
     * @param visitor class implementing the code generation
     */
    public abstract Module genCode( StatementTransform<Module> visitor );
    /** Debugging output of a statement at an indent level */
    public abstract String toString( int level );
    /** Debugging output at level 0 */
    @Override
    public String toString() {
        return this.toString(0);
    }

    /** Statement node representing an erroneous statement. */
    public static class ErrorNode extends StatementNode {
        public ErrorNode( Position pos, int pc ) {
            super( pos, pc );
        }
        @Override
        public void accept( StatementVisitor visitor ) {
            visitor.visitStatementErrorNode( this );
        }
        @Override
        public Module genCode( StatementTransform<Module> visitor ) {
            return visitor.visitStatementErrorNode( this );
        }
        @Override
        public String toString( int level) {
            return "ERROR";
        }
    }

    /** Tree node representing an assignment statement. */
    public static class AssignmentNode extends StatementNode {
        /** Tree node for expression on left hand side of an assignment. */
        private ExpNode variable;
        /** Tree node for the expression to be assigned. */
        private ExpNode exp;

        public AssignmentNode( Position pos, int pc, ExpNode variable, 
                ExpNode exp ) {
            super( pos, pc );
            this.variable = variable;
            this.exp = exp;
        }
        @Override
        public void accept( StatementVisitor visitor ) {
            visitor.visitAssignmentNode( this );
        }
        @Override
        public Module genCode( StatementTransform<Module> visitor ) {
            return visitor.visitAssignmentNode( this );
        }
        public ExpNode getVariable() {
            return variable;
        }
        public void setVariable( ExpNode variable ) {
            this.variable = variable;
        }
        public ExpNode getExp() {
            return exp;
        }
        public void setExp(ExpNode exp) {
            this.exp = exp;
        }
        public String getVariableName() {
            if( variable instanceof ExpNode.VariableNode ) {
                return 
                    ((ExpNode.VariableNode)variable).getVariable().getIdent();
            } else {
                return "<noname>";
            }
        }
        @Override
        public String toString( int level ) {
            return variable.toString() + " := " + exp.toString();
        }
    }
    /** Tree node representing a "write" statement. */
    public static class WriteNode extends StatementNode {
        private ExpNode exp;

        public WriteNode( Position pos, int pc, ExpNode exp ) {
            super( pos, pc );
            this.exp = exp;
        }
        @Override
        public void accept( StatementVisitor visitor ) {
            visitor.visitWriteNode( this );
        }
        @Override
        public Module genCode( StatementTransform<Module> visitor ) {
            return visitor.visitWriteNode( this );
        }
        public ExpNode getExp() {
            return exp;
        }
        public void setExp( ExpNode exp ) {
            this.exp = exp;
        }
        @Override
        public String toString( int level ) {
            return "WRITE " + exp.toString();
        }
    }
    
    /** Tree node representing a "call" statement. */
    public static class CallNode extends StatementNode {
        private String id;
        private SymEntry.ProcedureEntry procEntry;
        private ExpNode argsList;

        public CallNode( Position pos, int pc, String id, ExpNode argsList) {
            super( pos, pc );
            this.id = id;
            this.argsList = argsList;
        }
        @Override
        public void accept( StatementVisitor visitor ) {
            visitor.visitCallNode( this );
        }
        @Override
        public Module genCode( StatementTransform<Module> visitor ) {
            return visitor.visitCallNode( this );
        }
        public String getId() {
            return id;
        }
        public SymEntry.ProcedureEntry getEntry() {
            return procEntry;
        }
        public void setEntry(SymEntry.ProcedureEntry entry) {
            this.procEntry = entry;
        }
        @Override
        public String toString( int level ) {
            String s = "CALL " + id;
            return s + argsList.toString();
        }
    }
    /** Tree node representing a statement list. */
    public static class ListNode extends StatementNode {
        private List<StatementNode> statements;
        
        public ListNode( Position pos, int pc ) {
            super( pos, pc );
            this.statements = new ArrayList<StatementNode>();
        }
        public void addStatement( StatementNode s ) {
            statements.add( s );
        }
        @Override
        public void accept( StatementVisitor visitor ) {
            visitor.visitStatementListNode( this );
        }
        @Override
        public Module genCode( StatementTransform<Module> visitor ) {
            return visitor.visitStatementListNode( this );
        }
        public List<StatementNode> getStatements() {
            return statements;
        }
        @Override
        public String toString( int level) {
            String result = "";
            String sep = "";
            for( StatementNode s : statements ) {
                if(s == null) continue;
                result += sep + s.toString( level );
                sep = ";" + Tree.newLine(level);
            }
            return result;
        }
    }
    /** Tree node representing an "if" statement. */
    public static class IfNode extends StatementNode {
        private ExpNode condition;
        private StatementNode thenStmt;
        private StatementNode elseStmt;

        public IfNode( Position pos, int pc, ExpNode condition, 
                StatementNode thenStmt, StatementNode elseStmt ) {
            super( pos, pc );
            this.condition = condition;
            this.thenStmt = thenStmt;
            this.elseStmt = elseStmt;
        }
        @Override
        public void accept( StatementVisitor visitor ) {
            visitor.visitIfNode( this );
        }
        @Override
        public Module genCode( StatementTransform<Module> visitor ) {
            return visitor.visitIfNode( this );
        }
        public ExpNode getCondition() {
            return condition;
        }
        public void setCondition( ExpNode cond ) {
            this.condition = cond;
        }
        public StatementNode getThenStmt() {
            return thenStmt;
        }
        public StatementNode getElseStmt() {
            return elseStmt;
        }
        @Override
        public String toString( int level ) {
            return "IF " + condition.toString() + " THEN" + 
                        Tree.newLine(level+1) + thenStmt.toString( level+1 ) + 
                    Tree.newLine( level ) + "ELSE" + 
                        Tree.newLine(level+1) + elseStmt.toString( level+1 );
        }
    }
    
    /** Tree node representing an "CAS" statement. */
    public static class CasNode extends StatementNode {
        private ExpNode oldValue;
        private ExpNode compareValue;
        private ExpNode newValue;

        public CasNode( Position pos, int pc,  ExpNode oldValue, 
                ExpNode compareValue, ExpNode newValue) {
            super( pos, pc );
            this.compareValue = compareValue;
            this.oldValue = oldValue;
            this.newValue = newValue;
        }
        public ExpNode getOldValue() {
        	return oldValue;
        }
        public void setOldValue(ExpNode oldValue) {
        	this.oldValue = oldValue;
        }
        public ExpNode getNewValue() {
        	return newValue;
        }
        public void setNewValue(ExpNode newValue) {
        	this.newValue = newValue;
        }
        public ExpNode getCompareValue() {
        	return compareValue;
        }
        public void setCompareValue(ExpNode compareValue) {
        	this.compareValue = compareValue;
        }
        @Override
        public void accept( StatementVisitor visitor ) {
            visitor.visitCasNode( this );
        }
        @Override
        public Module genCode( StatementTransform<Module> visitor ) {
            return visitor.visitCasNode( this );
        }
        @Override
        public String toString( int level ) {
            return "CAS(" + oldValue.toString() + ", " + 
            		compareValue.toString() + ", " + newValue.toString() + 
            		")";
        }
    }

    /** Tree node representing a "while" statement. */
    public static class WhileNode extends StatementNode {
        private ExpNode condition;
        private StatementNode loopStmt;
        private int endPc;

        public WhileNode( Position pos, int pc, ExpNode condition, 
              StatementNode loopStmt ) {
            super( pos, pc );
            this.condition = condition;
            this.loopStmt = loopStmt;
        }
        @Override
        public void accept( StatementVisitor visitor ) {
            visitor.visitWhileNode( this );
        }
        @Override
        public Module genCode( StatementTransform<Module> visitor ) {
            return visitor.visitWhileNode( this );
        }
        public ExpNode getCondition() {
            return condition;
        }
        public void setCondition( ExpNode cond ) {
            this.condition = cond;
        }
        public int getEndPc() {
            return endPc;
        }
        public void setEndPc( int pc ) {
            this.endPc = pc;
        }
        public StatementNode getLoopStmt() {
            return loopStmt;
        }
        public void setLoopStatement(StatementNode loopStmt) {
            this.loopStmt = loopStmt;
        }
        @Override
        public String toString( int level ) {
            return "WHILE " + condition.toString() + " DO" +
                Tree.newLine(level+1) + loopStmt.toString( level+1 );
        }
    }
    /** Tree node representing a "do-while" statement*/
    public static class DoWhileNode extends StatementNode {
        private ExpNode condition;
        private StatementNode loopStmt;
        private int endPc;

        public DoWhileNode( Position pos, int pc, ExpNode condition, 
              StatementNode loopStmt ) {
            super( pos, pc );
            this.condition = condition;
            this.loopStmt = loopStmt;
        }
        @Override
        public void accept( StatementVisitor visitor ) {
            visitor.visitDoWhileNode( this );
        }
        @Override
        public Module genCode( StatementTransform<Module> visitor ) {
            return visitor.visitDoWhileNode( this );
        }
        public ExpNode getCondition() {
            return condition;
        }
        public void setCondition( ExpNode cond ) {
            this.condition = cond;
        }
        public int getEndPc() {
            return endPc;
        }
        public void setEndPc( int pc ) {
            this.endPc = pc;
        }
        public StatementNode getLoopStmt() {
            return loopStmt;
        }
        public void setLoopStatement( StatementNode loopStmt ) {
            this.loopStmt = loopStmt;
        }
        @Override
        public String toString( int level ) {
            return "DO" + Tree.newLine(level+1) + loopStmt.toString( level+1 ) + 
            		Tree.newLine(level) + "WHILE " + condition.toString();
        }
    }
    /** Tree node representing a "repeat-until" statement*/
    public static class RepeatUntilNode extends StatementNode {
        private ExpNode condition;
        private StatementNode loopStmt;
        private int endPc;

        public RepeatUntilNode( Position pos, int pc,  ExpNode condition, 
              StatementNode loopStmt ) {
            super( pos, pc );
            this.condition = condition;
            this.loopStmt = loopStmt;
        }
        @Override
        public void accept( StatementVisitor visitor ) {
            visitor.visitRepeatNode( this );
        }
        @Override
        public Module genCode( StatementTransform<Module> visitor ) {
            return visitor.visitRepeatNode( this );
        }
        public ExpNode getCondition() {
            return condition;
        }
        public void setCondition( ExpNode cond ) {
            this.condition = cond;
        }
        public int getEndPc() {
            return endPc;
        }
        public void setEndPc( int pc ) {
            this.endPc = pc;
        }
        public StatementNode getLoopStmt() {
            return loopStmt;
        }
        public void setLoopStatement(StatementNode loopStmt) {
            this.loopStmt = loopStmt;
        }
        @Override
        public String toString( int level ) {
            return "REPEAT" + Tree.newLine(level+1) + loopStmt.toString( level+1 ) + 
                    Tree.newLine(level) + "UNTIL " + condition.toString();
        }
    }
    
    /** Tree node representing a "emtpy" statement. */
    public static class EmptyNode extends StatementNode {

        public EmptyNode(Position pos, int pc ) {
            super( pos, pc );
        }
        /** Provides access to the visitor pattern over trees
         * which is used for static checking and code generation. */
        @Override
        public void accept( StatementVisitor visitor ) {
            ;
        }
        /** provides visitor transformation pattern for code generation */
        @Override
        public Module genCode( StatementTransform<Module> visitor ) {
            return new Module();
        }
        /** For debugging purposes. */
        @Override
        public String toString( int level ) {
            return "";
        }
    }
    
    /** Tree node representing a "break" statement. */
    public static class BreakNode extends StatementNode {
        private StatementNode enclosingLoop;
        
        public BreakNode(Position pos, int pc, StatementNode enclosingLoop) {
            super( pos, pc );
            this.enclosingLoop = enclosingLoop;
        }
        public StatementNode getEnclosingLoop() {
            return this.enclosingLoop;
        }
        
        /** Provides access to the visitor pattern over trees
         * which is used for static checking and code generation. */
        @Override
        public void accept( StatementVisitor visitor ) {
            visitor.visitBreakNode( this );
        }
        /** provides visitor transformation pattern for code generation */
        @Override
        public Module genCode( StatementTransform<Module> visitor ) {
            return visitor.visitBreakNode( this );
        }
        /** For debugging purposes. */
        @Override
        public String toString( int level ) {
            return "break";
        }
    }
    
    /** Tree node representing a "continue" statement. */
    public static class ContinueNode extends StatementNode {
        private StatementNode enclosingLoop;
        
        public ContinueNode(Position pos, int pc, StatementNode enclosingLoop) {
            super( pos, pc );
            this.enclosingLoop = enclosingLoop;
        }
        public StatementNode getEnclosingLoop() {
            return this.enclosingLoop;
        }
        
        /** Provides access to the visitor pattern over trees
         * which is used for static checking and code generation. */
        @Override
        public void accept( StatementVisitor visitor ) {
            visitor.visitContinueNode( this );
        }
        /** provides visitor transformation pattern for code generation */
        @Override
        public Module genCode( StatementTransform<Module> visitor ) {
            return visitor.visitContinueNode( this );
        }
        /** For debugging purposes. */
        @Override
        public String toString( int level ) {
            return "continue";
        }
    }
    
    /** Tree node representing a "return" statement. */
    public static class ReturnNode extends StatementNode {
        private List<ExpNode> retVals;
        private String procedure;
        private boolean isEmpty;
    
        public ReturnNode(Position pos, int pc, List<ExpNode> retVals, String procedure, boolean isEmpty) {
            super( pos, pc );
            this.retVals = retVals;
            this.procedure = procedure;
            this.isEmpty = isEmpty;
        }
        public List<ExpNode> getRetVals() {
            return retVals;
        }
        public void setRetVals(List<ExpNode> retVals) {
        	this.retVals = retVals;
        }
        public String getProcedure() {
        	return procedure;
        }
        public boolean isEmpty() {
        	return isEmpty;
        }
        /** Provides access to the visitor pattern over trees
         * which is used for static checking and code generation. */
        @Override
        public void accept( StatementVisitor visitor ) {
            visitor.visitReturnNode( this );
        }
        /** provides visitor transformation pattern for code generation */
        @Override
        public Module genCode( StatementTransform<Module> visitor ) {
            return visitor.visitReturnNode( this );
        }
        /** For debugging purposes. */
        @Override
        public String toString( int level ) {
            if(retVals == null) return "return";
            return "return " + Arrays.toString(retVals.toArray());
        }
    }
    
    /** Tree node representing a "lock" statement. */
    public static class LockNode extends StatementNode {
    
        public LockNode(Position pos, int pc) {
            super( pos, pc );
        }
        /** Provides access to the visitor pattern over trees
         * which is used for static checking and code generation. */
        @Override
        public void accept( StatementVisitor visitor ) {
            visitor.visitLockNode( this );
        }
        /** provides visitor transformation pattern for code generation */
        @Override
        public Module genCode( StatementTransform<Module> visitor ) {
            return visitor.visitLockNode( this );
        }
        /** For debugging purposes. */
        @Override
        public String toString( int level ) {
            return "LOCK";
        }
    }
    
    /** Tree node representing a "lock" statement. */
    public static class UnlockNode extends StatementNode {
    
        public UnlockNode(Position pos, int pc) {
            super( pos, pc );
        }
        /** Provides access to the visitor pattern over trees
         * which is used for static checking and code generation. */
        @Override
        public void accept( StatementVisitor visitor ) {
            visitor.visitUnlockNode( this );
        }
        /** provides visitor transformation pattern for code generation */
        @Override
        public Module genCode( StatementTransform<Module> visitor ) {
            return visitor.visitUnlockNode( this );
        }
        /** For debugging purposes. */
        @Override
        public String toString( int level ) {
            return "UNLOCK";
        }
    }
}

