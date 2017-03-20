package tree;
import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;

import source.Errors;
import syms.Predefined;
import syms.Scope;
import syms.SymEntry;
import syms.SymbolTable;
import syms.Type;
import syms.Type.IncompatibleTypes;
import tree.DeclNode.DeclListNode;
import tree.DeclNode.VarListNode;
import tree.StatementNode.DoWhileNode;
import tree.Tree.*;

/** class StaticSemantics - Performs the static semantic checks on
 * the abstract syntax tree using a visitor pattern to traverse the tree.
 * @version $Revision: 22 $  $Date: 2014-05-20 15:14:36 +1000 (Tue, 20 May 2014) $
 * See the notes on the static semantics of PL0 to understand the PL0
 * type system in detail.
 */
public class StaticChecker implements TreeVisitor, StatementVisitor, 
                                        ExpTransform<ExpNode> {

    /** The static checker maintains a symbol table reference.
     * Its current scope is that for the procedure 
     * currently being processed.
     */
    private SymbolTable symtab;
    /** Errors are reported through the error handler. */
    private Errors errors;
    /** Keep track of return type of any function currently being cheked */
    private List<Type> returnTypes = null;

    /** Construct a static checker for PL0.
     * @param errors is the error message handler.
     */
    public StaticChecker( Errors errors ) {
        super();
        this.errors = errors;
    }
    /** The tree traversal starts with a call to visitProgramNode.
     * Then its descendants are visited using visit methods for each
     * node type, which are called using the visitor pattern "accept"
     * method (or "transform" for expression nodes) of the abstract
     * syntax tree node.
     */
    public void visitProgramNode(ProgramNode node) {
        // Set up the symbol table to be that for the main program.
        symtab = node.getBaseSymbolTable();
        // Set the current symbol table scope to that for the procedure.
        symtab.reenterScope( node.getBlock().getBlockLocals() );
        // resolve all references to identifiers with the declarations
        symtab.resolveCurrentScope();
        // Check the main program block.
        node.getBlock().accept( this );
        //System.out.println( node );
    }
    public void visitBlockNode(BlockNode node) {
        // Check the procedures, if any.
        node.getProcedures().accept( this );
        // Check the body of the block.
        node.getBody().accept( this );
        // System.out.println( symtab );
        // Restore the symbol table to the parent scope (not really necessary)
        symtab.leaveScope();
        //System.out.println( "Block Body\n" + node.getBody() );
    }
    public void visitDeclListNode(DeclListNode node) {
        for( DeclNode declaration : node.getDeclarations() ) {
            declaration.accept( this );
        }
    }
    /** Procedure, function or main program node */
    public void visitProcedureNode(DeclNode.ProcedureNode node) {
        SymEntry.ProcedureEntry procEntry = node.getProcEntry();
        returnTypes = procEntry.getReturnTypes();
        int i=0;
        for(Type returnType : returnTypes) {
           returnTypes.set(i, returnType.resolveType(procEntry.getPosition()));
           i++;
        }
        // Set the current symbol table scope to that for the procedure.
        symtab.reenterScope( procEntry.getLocalScope() );
        // resolve all references to identifiers with the declarations
        symtab.resolveCurrentScope();
        // Check the block of the procedure.
        node.getBlock().accept( this );
        //returnType = null;
    }
    /*************************************************
     *  Statement node static checker visit methods
     *************************************************/
    public void visitStatementErrorNode(StatementNode.ErrorNode node) {
        // Nothing to check - already invalid.
    }

    public void visitAssignmentNode(StatementNode.AssignmentNode node) {
        // Check the left side left value.
        ExpNode left = node.getVariable().transform( this );
        node.setVariable( left );
        // Check the right side expression.
        ExpNode exp = node.getExp().transform( this );
        node.setExp( exp );
        // Validate that it is a true left value and not a constant.
        Type lvalType = left.getType();
        if( ! (lvalType instanceof Type.ReferenceType) ) {
            errors.error( "variable (i.e., L-Value) expected", left.getPosition() );
        } else {
            /* Validate that the right expression is assignment
             * compatible with the left value. This may require that the 
             * right side expression is coerced to the dereferenced
             * type of the left side LValue. */
            Type baseType = ((Type.ReferenceType)lvalType).getBaseType();
            node.setExp( baseType.coerceExp( exp ) );
        }
    }

    public void visitWriteNode(StatementNode.WriteNode node) {
        // Check the expression being written.
        ExpNode exp = node.getExp().transform( this );
        // coerce expression to be of type integer,
        // or complain if not possible.
        node.setExp( Predefined.INTEGER_TYPE.coerceExp( exp ) );
    }

    public void visitCallNode(StatementNode.CallNode node) {
        SymEntry.ProcedureEntry procEntry;
        // Look up the symbol table entry for the procedure.
        SymEntry entry = symtab.lookup( node.getId() );
        if( entry instanceof SymEntry.ProcedureEntry ) {
            procEntry = (SymEntry.ProcedureEntry)entry;
            node.setEntry( procEntry );
            //TODO: Future work - Check arguments here if we allow procedure calls
        } else {
            errors.error( "Procedure identifier required", node.getPosition() );
            return;
        }
    }
    
    public void visitBreakNode(StatementNode.BreakNode node) {
        if(node.getEnclosingLoop() == null) {
            errors.error("'Break' must be contained in a loop statement", node.getPosition() );
        }
        
    }
    
    public void visitContinueNode(StatementNode.ContinueNode node) {
        if(node.getEnclosingLoop() == null) {
            errors.error("'Continue' must be contained in a loop statement", node.getPosition() );
        }
    }
    
    public void visitReturnNode(StatementNode.ReturnNode node) {
        List<ExpNode> retVals = new ArrayList<ExpNode>();
        // Check the number of actual parameters being returned matches the number of formal return parameters
        if(node.getRetVals().size() != returnTypes.size()) {
            errors.error("Number of return parameters must match number of return types in procedure head", node.getPosition() );
        }
        for(int i=0; i < node.getRetVals().size(); i++) {
            Type returnType = returnTypes.get(i);
            ExpNode val = node.getRetVals().get(i);
            
            // Check return value actual type against formal type
            if(node.isEmpty()) {
                if(!(returnType instanceof Type.VoidType)) {
                    errors.error("Cannot have empty return statement for non-void function", node.getPosition() );
                }
                return;
            }
            if(returnType == null) {
                errors.error( "No valid return type specified in function header", node.getPosition() );
                return;
            }
            ExpNode retVal = val.transform( this );
            retVals.add(returnType.coerceExp(retVal));
        }
        
        node.setRetVals(retVals);
    }

    public void visitStatementListNode( StatementNode.ListNode node ) {
        for( StatementNode s : node.getStatements() ) {
            if(s == null) continue;
            s.accept( this );
        }
    }
    private ExpNode checkCondition( ExpNode cond ) {
        // Check and transform the condition
        cond = cond.transform( this );
        /* Validate that the condition is boolean, which may require
         * coercing the condition to be of type boolean. */     
        return Predefined.BOOLEAN_TYPE.coerceExp( cond );
    }
    public void visitIfNode(StatementNode.IfNode node) {
        // Check the condition.
        node.setCondition( checkCondition( node.getCondition() ) );
        // Check the 'then' part.
        node.getThenStmt().accept( this );
        // Check the 'else' part.
        node.getElseStmt().accept( this );
    }

    public void visitWhileNode(StatementNode.WhileNode node) {
        // Check the condition.
        node.setCondition( checkCondition( node.getCondition() ) );
        // Check the body of the loop.
        node.getLoopStmt().accept( this );
    }
    
    public void visitRepeatNode(StatementNode.RepeatUntilNode node) {
        // Check the condition.
        node.setCondition( checkCondition( node.getCondition() ) );
        // Check the body
        node.getLoopStmt().accept( this);
    }
    
    public void visitDoWhileNode(StatementNode.DoWhileNode node) {
        // Check the condition.
        node.setCondition( checkCondition( node.getCondition() ) );
        // Check the body
        node.getLoopStmt().accept( this);
    }
    /**
     * Visiting a CAS statement, for example CAS(a, b, c); Since a CAS is 
     * just an equivalence check and an assignment, we can utilise
     * these nodes to perform an equivalent static check.
     */
    public void visitCasNode(StatementNode.CasNode node) {
        node.setNewValue(node.getNewValue().transform(this));
        node.setOldValue(node.getOldValue().transform(this));
        node.setCompareValue(node.getCompareValue().transform(this));
        // Check the component that compares the first two arguments
        visitOperatorNode(new ExpNode.OperatorNode(node.getPosition(), Operator.EQUALS_OP, 
                new ExpNode.ArgumentsNode(node.getOldValue(), node.getCompareValue())));
        // Check the component that assigns the third argument to the first
        visitAssignmentNode(new StatementNode.AssignmentNode(node.getPosition(), -1, 
                node.getOldValue(), node.getNewValue()));
    }
    
    public void visitLockNode(StatementNode.LockNode node) {
        // Nothing to do
    }
    
    public void visitUnlockNode(StatementNode.UnlockNode node) {
        // Nothing to do
    }
    
    /*************************************************
     *  Expression node static checker visit methods
     *************************************************/
    public ExpNode visitErrorExpNode(ExpNode.ErrorNode node) {
        // Nothing to do - already invalid.
        return node;
    }

    public ExpNode visitConstNode(ExpNode.ConstNode node) {
        // type already set up
        return node;
    }
    /** Reads an integer value from input */
    public ExpNode visitReadNode(ExpNode.ReadNode node) {
        // type already set up
        return node;
    }
    /** Handles binary and unary operators, 
     * allowing the types of operators to be overloaded.
     */
    public ExpNode visitOperatorNode( ExpNode.OperatorNode node ) {
        /* Operators can be overloaded */
        /* Check the argumments to the operator */
        ExpNode arg = node.getArg().transform( this );
        /* Lookup the operator in the symbol table to get its type */
        Type opType = symtab.lookupOperator(node.getOp().getName()).getType();
        if( opType instanceof Type.FunctionType ) {
            /* The operator is not overloaded. Its type is represented
             * by a FunctionType from its argument's type to its
             * result type.
             */
            Type.FunctionType fType = (Type.FunctionType)opType;
            node.setArg( fType.getArgType().coerceExp( arg ) );
            node.setType( fType.getResultType() );
        } else if( opType instanceof Type.IntersectionType ) {
            for( Type t : ((Type.IntersectionType)opType).getTypes() ) {
                /* The operator is overloaded. Its type is represented
                 * by an IntersectionType containing a set of possible
                 * types for the operator, each of which is a FunctionType.
                 * Each possible type is tried until one succeeds.
                 */
                Type.FunctionType fType = (Type.FunctionType)t;
                Type opArgType = fType.getArgType();
                try {
                    /* Coerce the argument to the argument type for 
                     * this operator type. If the coercion fails an
                     * exception will be trapped and an alternative 
                     * function type within the intersection tried.
                     */
                    ExpNode newArg = opArgType.coerceToType( arg );
                    /* The coercion succeeded if we get here */
                    node.setArg( newArg );
                    node.setType( fType.getResultType() );
                    return node;
                } catch ( IncompatibleTypes ex ) {
                    // Allow "for" loop to try an alternative
                }
            }
            // no match in intersection
            errors.error( "Type of argument " + arg.getType() + 
                    " does not match " + opType, node.getPosition() );
            node.setType( Type.ERROR_TYPE );
        } else {
            errors.fatal( "Invalid operator type", node.getPosition() );
        }
        return node;
    }
    /** An ArgumentsNode is used to represent a list of arguments, each 
     * of which is an expression. The arguments for a binary operator are 
     * represented by list with two elements.
     */
    public ExpNode visitArgumentsNode( ExpNode.ArgumentsNode node ) {
        List<ExpNode> newExps = new LinkedList<ExpNode>();
        List<Type> types = new LinkedList<Type>();
        for( ExpNode exp : node.getArgs() ) {
            ExpNode newExp = exp.transform( this );
            newExps.add( newExp );
            types.add( newExp.getType() );
        }
        node.setArgs( newExps );
        node.setType( new Type.ProductType( types ) );
        return node;
    }
    /** A DereferenceNode allows a variable (of type ref(int) say) to be
     * dereferenced to get its value (of type int). 
     */
    public ExpNode visitDereferenceNode(ExpNode.DereferenceNode node) {
        // Check the left value referred to by this right value.
        ExpNode lVal = node.getLeftValue().transform( this );
        node.setLeftValue( lVal );
        // The type of the right value is the base type of the left value.
        Type lValueType = lVal.getType();
        if( lValueType instanceof Type.ReferenceType ) {
            node.setType( lValueType.optDereference() ); // not optional here
        } else if( lValueType != Type.ERROR_TYPE ) {
            errors.error( "cannot dereference an expression which isn't a reference",
                    node.getPosition() );
        }
        return node;
    }
    
    /** When parsing an identifier within an expression one can't tell
     * whether it has been declared as a constant or an identifier.
     * Here we check which it is and return either a constant or 
     * a variable node.
     */
    public ExpNode visitIdentifierNode(ExpNode.IdentifierNode node) {
        // First we look up the identifier in the symbol table.
        ExpNode newNode;
        // Split the identifier in case its a property access
        String[] splitOnPeriod = node.getId().split("\\.");
        String id = splitOnPeriod.length > 0 ? splitOnPeriod[0] : node.getId();
        SymEntry entry = symtab.lookup( id );
        if( entry instanceof SymEntry.ConstantEntry ) {
            // Set up a new node which is a constant.
            SymEntry.ConstantEntry constEntry = 
                (SymEntry.ConstantEntry)entry;
            newNode = new ExpNode.ConstNode( node.getPosition(), 
                    constEntry.getType(), constEntry.getValue() );
        } else if( entry instanceof SymEntry.VarEntry ) {
            Type.ReferenceType type = (Type.ReferenceType) entry.getType();
            SymEntry.VarEntry varEntry = null;
            int index = -1;
            int length = 0;
            Type.ObjectType object = null;
            //TODO: Future work - Allow chaining of accesses to object attributes
            // If we are accessing a property of an object, check the property exists
            if(type.getBaseType() instanceof Type.ObjectType &&  splitOnPeriod.length > 1) {
                object = (Type.ObjectType) type.getBaseType();
                DeclNode.VarListNode variables = object.getVariables();
                List<String> vars = variables.getVars();
                List<Type> types = variables.getTypes();
                id = splitOnPeriod[1];
                Type newType = Type.ERROR_TYPE;
                length = vars.size();
                // Loop over instance variables until we find a match
                for(int i=0; i< vars.size(); i++) {
                    if (vars.get(i).equals(id)) {
                        newType = types.get(i);
                        index = i;
                        break;
                    }
                }
                if(newType == Type.ERROR_TYPE) {
                    errors.error(String.format("Property %s undefined for class %s", 
                            splitOnPeriod[1], splitOnPeriod[0]), node.getPosition() );
                }
                varEntry = new SymEntry.VarEntry(entry.getIdent(), entry.getPosition(),
                        new Scope(null, entry.getLevel(), null), new Type.ReferenceType(newType));
            } else {
                // Set up a new node which is a variable.
                varEntry = (SymEntry.VarEntry)entry;
            }
            newNode = new ExpNode.VariableNode(node.getPosition(), node.getId(), varEntry, index, length, object);
        } else {
            // Undefined identifier (or type or procedure identifier).
            // Set up new node to be an error node.
            newNode = new ExpNode.ErrorNode( node.getPosition() );
            errors.error("Constant or variable identifier required", node.getPosition() );
        }
        return newNode;
    }
    /**
     * Used to allocate a new object in memory, need to ensure we
     * are dealing with an object type, then update the variable to
     * have this type
     */
    public ExpNode visitNewObjectNode(ExpNode.NewObjectNode node) {
        // Ensure there is a symbol table entry fo this object type
        SymEntry entry = symtab.lookupType( node.getName() );
        if(entry == null) {
            errors.error(String.format("%s is not a valid object type", node.getName()), node.getPosition());
        }
        // Only use 'new' syntax for object types
        if(!(entry.getType() instanceof Type.ObjectType)) {
            errors.error("Expecting an object type", node.getPosition());
        }
        node.type = entry.getType();
        return node;
    }

    public ExpNode visitVariableNode(ExpNode.VariableNode node) {
        // Type already set up
        return node;
    }
    public ExpNode visitNarrowSubrangeNode(ExpNode.NarrowSubrangeNode node) {
        // Nothing to do.
        return node;
    }

    public ExpNode visitWidenSubrangeNode(ExpNode.WidenSubrangeNode node) {
        // Nothing to do.
        return node;
    }
    
    public void visitVarListNode(VarListNode node) {
        // Nothing to do.
        return;
    }
    /**
     * Visiting a CAS expression, for example if(CAS(a, b, c). Since a CAS is 
     * just an equivalence check and an assignment, we can utilise
     * these nodes to perform an equivalent static check.
     */
    public ExpNode visitCasNode(ExpNode.CasNode node) {
        ExpNode.ArgumentsNode args = node.getArgs();
        node.setArgs(args.transform( this ));
        // Check the component that compares the first two arguments
        visitOperatorNode(new ExpNode.OperatorNode(node.getPosition(), Operator.EQUALS_OP, 
                new ExpNode.ArgumentsNode(args.getArgs().get(0), args.getArgs().get(1))));
        // Check the component that assigns the third argument to the first
        visitAssignmentNode(new StatementNode.AssignmentNode(node.getPosition(), -1, 
                args.getArgs().get(0), args.getArgs().get(2)));
        return node;
    }
}
