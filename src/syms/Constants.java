package syms;

public class Constants {
    public static int FALSE_VALUE = 0;
    public static int TRUE_VALUE = 1;
    
    public enum Mode {
        PER_LINE
    }
    
    public static String TRUE = "true";
    public static String TRUE_CONSTANT = "1";
    
    public static String THREAD_SUFFIX = "q";
    public static String THREAD_MODULE_SUFFIX = "_D";
    public static String TRUE_SUFFIX = "T";
    public static String FALSE_SUFFIX = "F";
    
    public static String EMPTY_CONSTANT = "empty";
    public static String SEQUENCE_MODEL_NAME = "FiniteSeq";
    public static String SEQUENCE_FILE_NAME = "FiniteSequences";
    public static String INIT_MODULE_NAME = "Init";
    
    public static String PC_VALUE_REGEX = "\\d+(.T|.F)?";
    public static String VARIABLE_NAME_REGEX = "[a-zA-Z0-9.]*";
    
    // If "In" is followed by an 'o' then we should get Inout not In
    public static String IN_REGEX = "(.*In)|(.*In^o.*)";
    public static String INOUT_REGEX = ".*Inout.*";
    public static String OUT_REGEX = ".*Out.*";
    
    public static String[] REQUIRED_INVARIANTS = {"ABS", "INV", "STATUS", "D", "AOP", "STATUSHELPER"};
    public static String[] STATUS_TRANSITIONS = {"IN_OUT", "IN_INOUT", "INOUT_OUT", "INOUT_IN"};
}
