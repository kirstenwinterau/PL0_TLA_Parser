package parser;

import java.io.IOException;

import parser.Scanner;
import source.ErrorHandler;
import source.Errors;
import source.Position;

public class TokenStream {
    
    /*************************** Instance Variables ************************/
    /** The lexical analyzer */
    private Scanner lex;
    /** The current token */
    private LexicalToken currentToken;
    /** Control verbose parser debugging output */
    private boolean debugParse;
    /** Track nesting depth in parsing rules */
    private int debugLevel = 0;
    /** The object to report errors to */
    private Errors errors = ErrorHandler.getErrorHandler();
    
    public TokenStream( Scanner lex, boolean debugParse ) throws IOException {
        this.lex = lex;
        this.debugParse = debugParse;
        currentToken = lex.next();      /* Initialise with first token */
    }
       
    /** Get the kind of the current token */
    public Token getKind() {
        return currentToken.getKind();
    }
    /** Get the position of the current token */
    public Position getPosn() {
        return currentToken.getPosn();
    }
    /** Get the name associated with the current token
     * @requires currentToken.kind == Token.IDENTIFIER
     */
    public String getName() {
        assert currentToken.getKind() == Token.IDENTIFIER;
        return currentToken.getName();
    }
    /** Get the integer value associated with the current token
     * @requires currentToken.kind == Token.NUMBER
     */
    public int getIntValue() {
        assert currentToken.getKind() == Token.NUMBER;
        return currentToken.getIntValue();
    }
    /** Check if current token matches given token
     * @param expected type of token expected to match current token
     */
    public boolean isMatch( Token expected ) {
        return currentToken.isMatch( expected );
    }
    /** Check if current token matches any of the set of tokens
     * @param tokenTypes set of token types expected to be matched
     */
    public boolean isIn( TokenSet tokenTypes ) {
        return currentToken.isIn( tokenTypes );
    }
    /** Match if token is known to be expected, otherwise there is an error in
     * the parser. This version used to move on to the next token and give 
     * debugging output if enabled. 
     * @param expected - token expected next in the input stream.
     */
    public void match( Token expected ) {
        errors.checkAssert( currentToken.isMatch( expected ), 
                "Match assertion failed on " + expected, getPosn() );
        debugMessage( "Matched " + currentToken.toString() );
        currentToken = lex.next();
    }
    /** Match a token equal to that expected.
     * If the current token is the expected token, it is skipped,
     * otherwise an error is reported and error recovery attempted.
     * For the error recovery, if the current token can follow the expected
     * token, then it is assumed that the expected token was omitted and
     * no error recovery is necessary, otherwise the current token is skipped.
     * If the current token is skipped then the next token may be the
     * expected token, if so, it is matched.
     * @param expected - token expected next in the input stream.
     * @param follows - set of tokens expected to follow the expected token.
     * @requires follows is nonempty
     */
    public void match( Token expected, TokenSet follows ) {
        if( currentToken.isMatch( expected ) ) {
            match( expected );
        } else {
            parseError( "Parse error, expecting '" + expected + "'" );
            /* If the current token may follow the expected token then
             * treat it as though the expected token was missing and
             * do no further error recovery.
             */ 
            if( ! currentToken.isIn( follows ) && 
                !currentToken.isMatch( Token.EOF ) ) {
                // Skip the erroneous token
                debugMessage( "Skipping " + currentToken.toString() );
                currentToken = lex.next();
                /* If after skipping, the (new) token is not the expected 
                 * token we do no further error recovery (in match at least).
                 */
                if( currentToken.isMatch( expected ) ) {
                    /* If after skipping the erroneous token we find 
                     * the expected token we match it
                     */
                    match( expected );
                }
            }
        }
    }
    /** Match when follow set is a single token
     * @param expected - token expected next in the input stream.
     * @param follows - single token that may follow
     */
    public void match( Token expected, Token follows ) {
        match( expected, new TokenSet( follows ) );
    }
    /** Skip tokens until one is found which is in the parameter set find. 
     * Used for error recovery. 
     * @param find - set of tokens: skip until one found in this set
     * @requires find.contains( Token.EOF ); 
     */
    private void skipTo( TokenSet find ) {
        while( ! currentToken.isIn( find ) ) {
            debugMessage( "Skipping " + currentToken.toString() );
            currentToken = lex.next();
        }
    }
    /** Begin a parsing rule. 
     * Ensure that the next token is in the set of tokens expected 
     * at the start of a grammar rule. If the current token is not one
     * of the expected tokens, skip until either an expected token or
     * a token in the recoverSet is found. If an expected token is
     * eventually found then return successfully (true) otherwise fail.
     * A successful beginRule increments the indentation level for
     * debugging messages. 
     * An error is reported if it isn't.
     * @param rule - name of the rule for use in error messages
     * @param expected - set of tokens expected at start of rule
     * @param recoverSet - set of tokens to recover at on a syntax error
     * @return true iff an expected token was (eventually) found.
     * @requires recoverSet.contains( Token.EOF )
     */
    public boolean beginRule( String rule, TokenSet expected,
            TokenSet recoverSet ) {
        debugMessage( "Begin parse " + rule + " recover on " + recoverSet );
        if( ! currentToken.isIn( expected ) ) {
            parseError( currentToken + " cannot start " + rule );
            /* skipping cannot fail as recoverSet contains end-of-file */
            skipTo( recoverSet.union( expected ) );
            if( !currentToken.isIn( expected ) ) {
                return false;
            }
        }
        /* Increase the indentation level if successful return */
        debugLevel++;
        return true;
    }
    /** Begin a parsing rule. 
     * Same as above, except that expected is a single token.
     * @param rule - name of the rule for use in error messages
     * @param expected - token expected at start of rule
     * @param recoverSet set of tokens to recover at on a syntax error
     * @return true iff an expected token was (eventually) found.
     * @requires recoverSet.contains( Token.EOF )
     */
    public boolean beginRule( String rule, Token expected,
            TokenSet recoverSet) {
        return beginRule( rule, new TokenSet( expected ), recoverSet );
    }
    /** Version of beginRule when failure indicates that there
     * is an error in the parser.
     * @param rule - name of the rule for use in error messages
     * @param expected - set of tokens expected at start of rule
     */
    public void beginRule( String rule, TokenSet expected ) {
        debugMessage( "Begin parse " + rule );
        debugLevel++;
        if( ! currentToken.isIn( expected ) ) {
            errors.fatal( currentToken + " cannot start " + rule, currentToken.getPosn() );
            // doesn't return from fatal error
        }
    }
    /** Version of beginRule when failure indicates that there
     * is an error in the parser.
     * Same as above, except that expected is a single token.
     * @param rule - name of the rule for use in error messages
     * @param expected - token expected at start of rule
     */
    public void beginRule( String rule, Token expected ) {
        beginRule( rule, new TokenSet( expected ) );
    }
    /** End a parsing rule.
     * Ensure that the current token is a member of the recovery set 
     * (i.e., something which an ancestor rule is expecting).
     * @param rule name of the rule for use in error messages
     * @param recoverSet set of tokens to recover at on a syntax error
     * @requires recoverSet.contains( Token.EOF);
     */
    public void endRule( String rule, TokenSet recoverSet ) {
        if( ! currentToken.isIn( recoverSet ) ) {
            parseError( currentToken + " cannot follow " + rule );
            // Skipping cannot fail as recoverSet must contain end of file (EOF)
            skipTo( recoverSet );
        }
        debugLevel--;  /* Decrease debugging level at end of rule */
        debugMessage( "End parse " + rule );
    }
    /**************************** Support Methods ***************************/
    /** Output debugging message if debug turned on */
    private void debugMessage( String msg ) {
        if( debugParse ) {
            /* Indent message by the level of nesting of parsing rules */
            String indent = "";
            for( int i = 1; i <= debugLevel; i++ ) {
                indent += " ";
            }
            errors.println( indent + msg );
        }
    }
    /** Error message handle for parsing errors */
    private void parseError( String msg ) {
        debugMessage( msg );
        errors.error( msg, currentToken.getPosn() );
    }
}
