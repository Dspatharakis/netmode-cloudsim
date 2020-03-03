/**
 * Interface for ErlangA and ErlangC queueing model objects.
 */
public interface MMcDelay {

    /**
     * Returns the probability that a client must enter the waiting queue :
     $Pr\{W > t \}$, where $W$ is the waiting time.
     @param server the number of servers.
     @return the probability of delay.
     */
    public double getProbDelay(int server);

    /**
     * Returns the service level, defined as : $Pr\{W < awt \}$, where $W$ is
     * the waiting time.
     @param server the number of servers.
     @param awt the acceptable waiting time.
     @return the service level.
     */
    public double getServiceLevel(int server, double awt);

    /**
     * Returns the minimal number of servers needed to satisfy a service level of  minSL.
     @param awt the acceptable waiting time.
     @param minSL the minimal service level target.
     @return the minimal number of servers required.
     */
    public int minServer(double awt, double minSL);
}
