package tla;

/**
 * Represents a pre and post status combination of a line of code
 * @author Kelly
 */
public class CompositeStatus {
    public enum Status { In, Out, Inout, Idle }

    public Status pre;
    public Status post;
    
    public CompositeStatus(Status pre, Status post) {
        this.pre = pre;
        this.post = post;
    }
    
    @Override
    public boolean equals(Object o) {
        if (!(o instanceof CompositeStatus)) return false;
        CompositeStatus n = (CompositeStatus) o;
        return (n.pre.equals(this.pre) && n.post.equals(this.post));
    }
    
    
}
