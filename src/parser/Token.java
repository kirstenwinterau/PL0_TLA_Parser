package parser;

/** enumeration Token - Defines the basic tokens returned from the lexical analyzer.
 * @version $Revision: 22 $  $Date: 2014-05-20 15:14:36 +1000 (Tue, 20 May 2014) $
 */
public enum Token {
    EOF( "End-of-file"),
    PLUS( "+" ),
    MINUS( "-" ),
    TIMES( "*"),
    DIVIDE( "/" ),
    LPAREN( "(" ),
    RPAREN( ")" ),
    LBRACKET( "[" ),
    RBRACKET( "]" ),
    LCURLY("{"),
    RCURLY("}"),
    SEMICOLON( ";" ),
    COLON( ":" ),
    ASSIGN( ":=" ),
    COMMA( "," ),
    PERIOD("."),
    RANGE( ".." ),
    EQUALS( "=" ),
    NEQUALS( "!=" ),
    LEQUALS( "<=" ),
    LESS( "<" ),
    GEQUALS( ">=" ),
    GREATER( ">" ),
    LOG_AND( "&&" ),
    LOG_OR( "||" ),
    LOG_NOT( "!" ),
    MODULO("%"),
    KW_ABSTRACT( "abstract" ),
    KW_BEGIN( "begin" ),
    KW_BREAK( "break" ),
    KW_CALL( "call" ),
    KW_CAS( "CAS" ),
    KW_CONST( "const" ),
    KW_CONTINUE( "continue" ),
    KW_DO( "do" ),
    KW_ELSE( "else" ),
    KW_END( "end" ),
    KW_GLOBAL( "global" ),
    KW_IF( "if" ),
    KW_LOCK( "lock" ),
    KW_NEW( "new" ),
    KW_OBJECT( "object" ),
    KW_PROCEDURE( "procedure" ),
    KW_REPEAT( "repeat" ),
    KW_RETURN( "return" ),
    KW_THEN( "then" ),
    KW_TYPE( "type" ),
    KW_UNLOCK( "unlock" ),
    KW_UNTIL( "until" ),
    KW_VAR( "var" ),
    KW_WHILE( "while" ),
    IDENTIFIER( "identifier" ),
    NUMBER( "number" ),
    ILLEGAL( "illegal" );
    
    /** The name of the token */
    String name;
    
    private Token( String name ) {
        this.name = name;
    }
    @Override
    public String toString() {
        return name;
    }
}
