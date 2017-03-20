package tree;

import java.util.LinkedList;
import java.util.List;
import java.util.ArrayList;

import syms.SymEntry;
import syms.Type;

/**
 * class DeclNode - Handles Declarations lists and procedures.
 * @version $Revision: 22 $  $Date: 2014-05-20 15:14:36 +1000 (Tue, 20 May 2014) $ 
 * DeclNode is an abstract class. 
 * The classes defined within DeclNode extend it.
 */
public abstract class DeclNode {
    
    /** Constructor */
    protected DeclNode() {
        super();
    }
    /** Simple visitor pattern implemented in subclasses */
    public abstract void accept( TreeVisitor visitor );
    /** Debugging output at level 0 */
    @Override
    public String toString() {
        return toString(0);
    }
    /** Debugging output of declarations */
    public abstract String toString( int level );
    /** Tree node representing a list of (procedure) declarations */
    public static class DeclListNode extends DeclNode {
        List<DeclNode> declarations;
        
        public DeclListNode() {
            declarations = new LinkedList<DeclNode>();
        }
        public List<DeclNode> getDeclarations() {
            return declarations;
        }
        public void addDeclaration( DeclNode declaration ) {
            declarations.add( declaration );
        }
        @Override
        public void accept(TreeVisitor visitor) {
            visitor.visitDeclListNode( this );
        }
        public String toString( int level ) {
            String s = "";
            for( DeclNode decl : declarations ) {
                s += Tree.newLine(level) + decl.toString(level);
            }
            return s;
        }
    }
    
    public static class VarListNode extends DeclNode {
        private List<String> vars;
        private List<Type> types;
        private List<Boolean> globalIndicators;
        private List<Boolean> abstractIndicators;
        
        public VarListNode() {
            vars = new ArrayList<String>();
            types = new ArrayList<Type>();
            globalIndicators = new ArrayList<Boolean>();
            abstractIndicators = new ArrayList<Boolean>();
        }
        public void addVar(String varName, Type type, boolean isGlobal, boolean isAbstract) {
            vars.add(varName);
            types.add(type);
            globalIndicators.add(isGlobal);
            abstractIndicators.add(isAbstract);
        }
        public List<String> getVars() {
            return vars;
        }
        public List<Type> getTypes() {
            return types;
        }
        public List<Boolean> getGlobalIndicators() {
            return globalIndicators;
        }
        public List<Boolean> getAbstractIndicators() {
            return abstractIndicators;
        }
        public void accept(TreeVisitor visitor) {
            visitor.visitVarListNode(this);
        }
        public String toString(int level) {
            return vars.toString();
        }
    }

    /** Tree node representing a single procedure. */
    public static class ProcedureNode extends DeclNode {
        private SymEntry.ProcedureEntry procEntry;
        private Tree.BlockNode block;
        // Pc for first line of procedure
        private int initPc;

        public ProcedureNode( SymEntry.ProcedureEntry entry, 
                Tree.BlockNode block, int initPc ) {
            this.procEntry = entry;
            this.block = block;
            this.initPc = initPc;
        }
        @Override
        public void accept( TreeVisitor visitor ) {
            visitor.visitProcedureNode( this );
        }
        public SymEntry.ProcedureEntry getProcEntry() {
            return procEntry;
        }
        public Tree.BlockNode getBlock() {
            return block;
        }
        public int getInitPc() {
            return initPc;
        }
        public String toString( int level ) {
            return "PROCEDURE " + procEntry.getIdent() +
                " = " + block.toString( level+1 );
        }
    }
}
