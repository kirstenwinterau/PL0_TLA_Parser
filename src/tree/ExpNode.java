package tree;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import source.Position;
import syms.Predefined;
import syms.SymEntry;
import syms.Type;
import tla.Module;

/** 
 * class ExpNode - Abstract Syntax Tree representation of expressions.
 * @version $Revision: 22 $  $Date: 2014-05-20 15:14:36 +1000 (Tue, 20 May 2014) $
 * Abstract class representing expressions.
 * The classes defined within ExpNode extend it.
 * All expression nodes have a position and a type.
 */
public abstract class ExpNode {
    /** Position in the source code of the expression */
    protected Position pos;
    /** Type of the expression (determined by static checker) */
    protected Type type;
    
    /** Constructor when type is known */
    protected ExpNode( Position pos, Type type) {
        this.pos = pos;
        this.type = type;
    }
    /** Constructor when type as yet unknown */
    protected ExpNode( Position pos ) {
        this( pos, Type.ERROR_TYPE );
    }
    public Type getType() {
        return type;
    }
    public void setType( Type type ) {
        this.type = type;
    }
    public Position getPosition() {
        return pos;
    }
    
    /** Each subclass of ExpNode must provide a transform method
     * to do type checking and transform the expression node to 
     * handle type coercions, etc.
     * @param visitor object that implements a traversal.
     * @return transformed expression node
     */
    public abstract ExpNode transform( ExpTransform<ExpNode> visitor );

    /** Each subclass of ExpNode must provide a genCode method
     * to visit the expression node to handle code generation.
     * @param visitor object that implements a traversal.
     * @return generated code
     */
    public abstract Module genCode( ExpTransform<Module> visitor );
        
    /** Tree node representing an erroneous expression. */
    public static class ErrorNode extends ExpNode {
        
        public ErrorNode( Position pos ) {
            super( pos, Type.ERROR_TYPE );
        }
        @Override
        public ExpNode transform( ExpTransform<ExpNode> visitor ) {
            return visitor.visitErrorExpNode( this );
        }
        @Override
        public Module genCode( ExpTransform<Module> visitor ) {
            return visitor.visitErrorExpNode( this );
        }
        @Override
        public String toString() {
            return "ErrorNode";
        }
    }

    /** Tree node representing a constant within an expression. */
    public static class ConstNode extends ExpNode {
        /** constant's value */
        private int value;

        public ConstNode( Position pos, Type type, int value ) {
            super( pos, type );
            this.value = value;
        }
        public int getValue() {
            return value;
        }
        @Override
        public ExpNode transform( ExpTransform<ExpNode> visitor ) {
            return visitor.visitConstNode( this );
        }
        @Override
        public Module genCode(ExpTransform<Module> visitor ) {
            return visitor.visitConstNode( this );
        }
        @Override
        public String toString( ) {
            return Integer.toString(value);
        }
    }
    
    /** Tree node representing a function call within an expression. */
    public static class CallNode extends ExpNode {
        /** constant's value */
        private StatementNode call;

        public CallNode( Position pos, StatementNode call ) {
            super( pos );
            this.call = call;
        }
        public StatementNode getCall() {
            return call;
        }
        @Override
        public ExpNode transform( ExpTransform<ExpNode> visitor ) {
            return null;
        }
        @Override
        public Module genCode(ExpTransform<Module> visitor ) {
            return null;
        }
        @Override
        public String toString( ) {
            return call.toString();
        }
    }

    /** Identifier node is used until the identifier can be resolved 
     * to be either a constant or a variable during the static 
     * semantics check phase. 
     */
    public static class IdentifierNode extends ExpNode {
        /** Name of the identifier */
        private String id;
        
        public IdentifierNode( Position pos, String id ) {
            super( pos );
            this.id = id;
        }
        public String getId() {
            return id;
        }
        @Override
        public ExpNode transform( ExpTransform<ExpNode> visitor ) {
            return visitor.visitIdentifierNode( this );
        }
        @Override
        public Module genCode(ExpTransform<Module> visitor ) {
            return visitor.visitIdentifierNode( this );
        }
        @Override
        public String toString() {
            return id;
        }
    }
    /** Tree node representing a variable. */
    public static class VariableNode extends ExpNode {
        /** Symbol table entry for the variable */
        protected SymEntry.VarEntry variable;
        private String name;
        private int index;
        private int tupleLength;
        private Type.ObjectType parentObject;
    
        public VariableNode( Position pos, String name, SymEntry.VarEntry variable ) {
            super( pos, variable.getType() );
            this.variable = variable;
            this.name = name;
            this.index = -1;
        }
        public VariableNode( Position pos, String name, SymEntry.VarEntry variable, 
        		int index, int tupleLength, Type.ObjectType parentObject ) {
            super( pos, variable.getType() );
            this.variable = variable;
            this.name = name;
            this.index = index;
            this.tupleLength = tupleLength;
            this.parentObject = parentObject;
        }
        public String getName() {
        	return name;
        }
        public SymEntry.VarEntry getVariable() {
            return variable;
        }
        public int getIndex() {
        	return index;
        }
        public boolean isObjectAttribute() {
        	return index != -1;
        }
        public int getTupleLength() {
        	return tupleLength; 
        }
        public Type.ObjectType getParentObject() {
        	return parentObject;
        }
        @Override
        public ExpNode transform( ExpTransform<ExpNode> visitor ) {
            return visitor.visitVariableNode( this );
        }
        @Override
        public Module genCode(ExpTransform<Module> visitor ) {
            return visitor.visitVariableNode( this );
        }
        @Override
        public String toString( ) {
            return name;
        }
    }
    /** Tree node representing a "read" expression. */
    public static class ReadNode extends ExpNode {

        public ReadNode( Position pos ) {
            super( pos, Predefined.INTEGER_TYPE );
        }
        @Override
        public ExpNode transform( ExpTransform<ExpNode> visitor ) {
            return visitor.visitReadNode( this );
        }
        @Override
        public Module genCode(ExpTransform<Module> visitor ) {
            return visitor.visitReadNode( this );
        }
        @Override
        public String toString( ) {
            return "Read";
        }
    }
    /** Tree node representing an empty argument */
    public static class EmptyNode extends ExpNode {

        public EmptyNode( Position pos ) {
            super( pos );
        }
        @Override
        public ExpNode transform( ExpTransform<ExpNode> visitor ) {
            return null;
        }
        @Override
        public Module genCode(ExpTransform<Module> visitor ) {
            return null;
        }
        @Override
        public String toString( ) {
            return "";
        }
    }
    /** Tree node for an operator. */
    public static class OperatorNode extends ExpNode {
        /** Operator, e.g. binary or unary operator */
        private Operator op;
        /** Argument(s) for operator. If more than one argument then this is
         * an ArgumentsNode 
         */
        private ExpNode arg;
        private boolean isCondition = true;
        private boolean negate;
        
        public OperatorNode( Position pos, Operator op, ExpNode arg ) {
            super( pos );
            this.op = op;
            this.arg = arg;
        }
        public OperatorNode( Position pos, Operator op, ExpNode arg, boolean negate) {
            super( pos );
            this.op = op;
            this.arg = arg;
            this.isCondition = true;
            this.negate = negate;
        }
        public Operator getOp() {
            return op;
        }
        public ExpNode getArg() {
            return arg;
        }
        public void setArg( ExpNode arg ) {
            this.arg = arg;
        }
        @Override
        public ExpNode transform( ExpTransform<ExpNode> visitor ) {
            return visitor.visitOperatorNode( this );
        }
        @Override
        public Module genCode(ExpTransform<Module> visitor ) {
            return visitor.visitOperatorNode( this );
        }
        @Override
        public String toString() {
        	if(this.isCondition && this.negate == true) {
        		return "!" + op.toString() + arg;
        	}
            return op.toString() + arg;
        }
        
    }
    
    /** Tree node for a CAS condition */
    public static class CasNode extends ExpNode {
    	private ArgumentsNode args;
    	private boolean negate;
    	
    	public CasNode(Position pos, ExpNode oldValue, 
    			ExpNode compareValue, ExpNode newValue, boolean negate) {
    		super(pos);
    		this.negate = negate;
    		List<ExpNode> argsList = new ArrayList<ExpNode>();
    		argsList.add(oldValue);
    		argsList.add(compareValue);
    		argsList.add(newValue);
    		this.args = new ArgumentsNode(argsList);
    	}
    	public void setArgs( ExpNode args ) {
    		this.args = (ArgumentsNode) args;
    	}
    	public ArgumentsNode getArgs() {
            return args;
        }
		@Override
		public ExpNode transform(ExpTransform<ExpNode> visitor) {
			return visitor.visitCasNode(this);
		}
		@Override
		public Module genCode(ExpTransform<Module> visitor) {
			return visitor.visitCasNode(this);
		}
		@Override
        public String toString() {
			String logicalOperator = (negate == true) ? "!" : "";
            return logicalOperator + "CAS" + args.toString();
        }
    }

    /** Tree node for a list of arguments */
    public static class ArgumentsNode extends ExpNode {
        /** List of arguments */
        private List<ExpNode> args;
        
        /** @requires args is non-empty */
        public ArgumentsNode( Type.ProductType t, List<ExpNode> args ) {
            super( args.get(0).getPosition(), t );
            this.args = args;
        }
        /** @requires args is non-empty */
        public ArgumentsNode( List<ExpNode> args ) {
            super( args.get(0).getPosition() );
            this.args = args;
        }
        /** @requires exps is non-empty */
        public ArgumentsNode( ExpNode... exps ) {
            this( Arrays.asList( exps ) );
        }
        public List<ExpNode> getArgs() {
            return args;
        }
        public void setArgs( List<ExpNode> args ) {
            this.args = args;
        }
        @Override
        public ExpNode transform(ExpTransform<ExpNode> visitor ) {
            return visitor.visitArgumentsNode( this );
        }
        @Override
        public Module genCode(ExpTransform<Module> visitor ) {
            return visitor.visitArgumentsNode( this );
        }
        @Override
        public String toString() {
            String s = args.toString();
            if(s.length() > 1) {
            	s = s.substring(1, s.length() - 1);
            }
            return "(" + s + ")";
        }
    }

    /** Tree node for dereferencing an LValue.
     * A Dereference node references an ExpNode node and represents the
     * dereferencing of the "address" given by the leftValue to give
     * the value at that address.
     */
    public static class DereferenceNode extends ExpNode {
        /** LValue to be dereferenced */
        private ExpNode leftValue;

        public DereferenceNode( Type type, ExpNode exp ) {
            super( exp.getPosition(), type );
            this.leftValue = exp;
        }
        public ExpNode getLeftValue() {
            return leftValue;
        }
        public void setLeftValue( ExpNode leftValue ) {
            this.leftValue = leftValue;
        }
        @Override
        public ExpNode transform( ExpTransform<ExpNode> visitor ) {
            return visitor.visitDereferenceNode( this );
        }
        @Override
        public Module genCode(ExpTransform<Module> visitor ) {
            return visitor.visitDereferenceNode( this );
        }
        @Override
        public String toString( ) {
            return leftValue.toString();
        }
    }

    /** Tree node representing a coercion that narrows a subrange */
    public static class NarrowSubrangeNode extends ExpNode {
        /** Expression to be narrowed */
        private ExpNode exp;

        /* @requires type instance of Type.SubrangeType */
        public NarrowSubrangeNode( Position pos, Type.SubrangeType type, 
                ExpNode exp )
        {
            super( pos, type );
            this.exp = exp;
        }
        public Type.SubrangeType getSubrangeType() {
            return (Type.SubrangeType)getType();
        }
        public ExpNode getExp() {
            return exp;
        }
        @Override
        public ExpNode transform( ExpTransform<ExpNode> visitor ) {
            return visitor.visitNarrowSubrangeNode( this );
        }
        @Override
        public Module genCode(ExpTransform<Module> visitor ) {
            return visitor.visitNarrowSubrangeNode( this );
        }
        @Override
        public String toString() {
            return "NarrowSubrange(" + exp + ":" + getType() + ")";
        }
    }
    
    /** Tree node representing a widening of a subrange */
    public static class WidenSubrangeNode extends ExpNode {
        /** Expression to be widened */
        private ExpNode exp;

        /* @requires exp.getType() instanceof Type.SubrangeType */
        public WidenSubrangeNode( Position pos, Type type, ExpNode exp ) {
            super( pos, type );
            assert exp.getType() instanceof Type.SubrangeType;
            this.exp = exp;
        }
        public ExpNode getExp() {
            return exp;
        }
        @Override
        public ExpNode transform( ExpTransform<ExpNode> visitor ) {
            return visitor.visitWidenSubrangeNode( this );
        }
        @Override
        public Module genCode(ExpTransform<Module> visitor ) {
            return visitor.visitWidenSubrangeNode( this );
        }
        @Override
        public String toString() {
            return "WidenSubrange(" + exp + ":" + getType() + ")";
        }
    }
    
    // Node representing the instantiation of a new object
    public static class NewObjectNode extends ExpNode {
    	// Type of object
    	private String name;
    	
    	public NewObjectNode( Position pos, String name ) {
    		super( pos );
    		this.name = name;
    		type = Type.ERROR_TYPE;
    	}
    	
    	public String getName() {
    		return name;
    	}

		@Override
		public ExpNode transform(ExpTransform<ExpNode> visitor) {
			return visitor.visitNewObjectNode( this );
		}

		@Override
		public Module genCode(ExpTransform<Module> visitor) {
			return null;
		}
		@Override
        public String toString() {
            return "New(" + name + ")";
        }
    }

}
