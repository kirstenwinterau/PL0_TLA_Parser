package syms;

import source.Position;
import syms.Type.FunctionType;
import syms.Type.GenericType;
import syms.Type.ProductType;
import syms.Type.ScalarType;

public class Predefined {
    /** Predefined integer type. */
    public static ScalarType INTEGER_TYPE;
    /** Predefined boolean type. */
    public static ScalarType BOOLEAN_TYPE;
    public static GenericType GENERIC_TYPE;
    public static Type.ProductType PAIR_INTEGER_TYPE;   
    public static Type.ProductType PAIR_BOOLEAN_TYPE;           
    public static Type.ProductType PAIR_GENERIC_TYPE;
    public static Type.FunctionType ARITHMETIC_BINARY;
    public static Type.FunctionType INT_RELATIONAL_TYPE;    
    public static Type.FunctionType LOGICAL_BINARY;
    public static Type.FunctionType ARITHMETIC_UNARY;   
    public static Type.FunctionType LOGICAL_UNARY;
    public static Type.FunctionType GENERIC_UNARY;
    public static Type.FunctionType GENERIC_BINARY;
    
    public static void addPredefinedEntries( SymbolTable symtab ) {
        // Define types needed for predefined entries
        /** Predefined integer type. */
        INTEGER_TYPE = new ScalarType( 
                        Integer.MIN_VALUE, Integer.MAX_VALUE ) {
                    @Override
                    public String toString() { 
                        return "INT"; 
                    }
                };
        /** Predefined boolean type. */
        BOOLEAN_TYPE = new ScalarType( Constants.FALSE_VALUE, Constants.TRUE_VALUE ) {
                @Override
                public String toString() { 
                    return "BOOLEAN"; 
                }
            };
        GENERIC_TYPE = new GenericType("");
        PAIR_INTEGER_TYPE = new ProductType( INTEGER_TYPE, INTEGER_TYPE );                  
        PAIR_BOOLEAN_TYPE = new ProductType( BOOLEAN_TYPE, BOOLEAN_TYPE );
        ARITHMETIC_BINARY = new FunctionType( PAIR_INTEGER_TYPE, INTEGER_TYPE );
        INT_RELATIONAL_TYPE = new FunctionType( PAIR_INTEGER_TYPE, BOOLEAN_TYPE );
        PAIR_GENERIC_TYPE = new ProductType( GENERIC_TYPE, GENERIC_TYPE );
        LOGICAL_BINARY = new FunctionType( PAIR_BOOLEAN_TYPE, BOOLEAN_TYPE );
        ARITHMETIC_UNARY = new FunctionType( INTEGER_TYPE, INTEGER_TYPE );
        LOGICAL_UNARY = new FunctionType( BOOLEAN_TYPE, BOOLEAN_TYPE );
        GENERIC_UNARY = new FunctionType( GENERIC_UNARY, BOOLEAN_TYPE );
        GENERIC_BINARY = new FunctionType( PAIR_GENERIC_TYPE, BOOLEAN_TYPE );
        // Add predefined symbols to predefined scope
        symtab.addType( "int", Position.NO_POSITION, INTEGER_TYPE );
        symtab.addType( "boolean", Position.NO_POSITION, BOOLEAN_TYPE );
        symtab.addConstant("false", Position.NO_POSITION, BOOLEAN_TYPE, 
                Constants.FALSE_VALUE );
        symtab.addConstant("true", Position.NO_POSITION, BOOLEAN_TYPE, 
                Constants.TRUE_VALUE );
        symtab.addOperator("-_", Position.NO_POSITION, ARITHMETIC_UNARY );
        symtab.addOperator("_+_", Position.NO_POSITION, ARITHMETIC_BINARY );
        symtab.addOperator("_-_", Position.NO_POSITION, ARITHMETIC_BINARY );
        symtab.addOperator("_*_", Position.NO_POSITION, ARITHMETIC_BINARY );
        symtab.addOperator("_/_", Position.NO_POSITION, ARITHMETIC_BINARY );
        symtab.addOperator("_%_", Position.NO_POSITION, ARITHMETIC_BINARY);
        symtab.addOperator("_=_", Position.NO_POSITION, INT_RELATIONAL_TYPE );
        symtab.addOperator("_=_", Position.NO_POSITION, LOGICAL_BINARY );
        symtab.addOperator("_=_", Position.NO_POSITION, GENERIC_BINARY );
        symtab.addOperator("_!=_", Position.NO_POSITION, INT_RELATIONAL_TYPE );
        symtab.addOperator("_!=_", Position.NO_POSITION, LOGICAL_BINARY );
        symtab.addOperator("_!=_", Position.NO_POSITION, GENERIC_BINARY );
        symtab.addOperator("_>_", Position.NO_POSITION, INT_RELATIONAL_TYPE);
        symtab.addOperator("_<_", Position.NO_POSITION, INT_RELATIONAL_TYPE);
        symtab.addOperator("_>=_", Position.NO_POSITION, INT_RELATIONAL_TYPE);
        symtab.addOperator("_<=_", Position.NO_POSITION, INT_RELATIONAL_TYPE);
        symtab.addOperator("_&&_", Position.NO_POSITION, LOGICAL_BINARY );
        symtab.addOperator("_||_", Position.NO_POSITION, LOGICAL_BINARY );
        symtab.addOperator("!_", Position.NO_POSITION, LOGICAL_UNARY );
        symtab.addOperator("!_", Position.NO_POSITION, GENERIC_UNARY );
    }
}
