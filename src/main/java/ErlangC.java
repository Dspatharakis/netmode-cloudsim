/**
     * The Erlang C formula is used to compute the delay probability $Pr\{ W > 0 \}$
     * and also the service level, defined as $Pr\{ W \le awt\}$, where $W$ is the
     * waiting time and $awt$ the acceptable waiting time.
     * This formula assumes a $M/M/c$ queueing model such that the arrival and
     * service rates are exponential.
     * The $M/M/c$ assumes one call type and one agent group.
     * This queueing model can be analyzed as a stochastic process
     * $X(t) \in \{0, \dots, c+q \}$
     * representing the number of calls in the system at time $t$ and where
     * $c+q$ is maximum number of calls in the system. The number of servers is $c$
     * and the capacity of the queue is $q$.
     * Calls are blocked when the system is at full, $X(t) = c+q$.
     * It assumes no abandonment due to the impatience of the client.
     *
     * The rates at each state are :
     \[
     \begin{array}{lll}
     \lambda_k = & \lambda, & k = 1, 2, \dots, c+q-1 \\
     \mu_k = & \left \{
     \begin{array}{ll}
     k \mu, \\
     c \mu,
     \end{array} \right .
     &
     \begin{array}{l}
     k = 1, 2, \dots, c-1 \\
     k = c, c+1, \dots, c+q .
     \end{array}
     \end{array}
     \]
     */
    public class ErlangC implements MMcDelay {

        private double arrivalRate = -1;
        private double serviceRate = -1;
        private int    capacity = -1;

        /** Creates a new instance of ErlangC. Set the capacity to {@link Integer#MAX_VALUE}
         * for infinite queue capacity.
         *
         @param arrivalRate the arrival rate.
         @param serviceRate the service rate.
         @param capacity the capacity of the queue.
         */
        public ErlangC(double arrivalRate, double serviceRate, int capacity) {
            if (arrivalRate < 0 || serviceRate < 0 || capacity < 0)
                throw new IllegalArgumentException("The arguments cannot be negative!");

            this.arrivalRate = arrivalRate;
            this.serviceRate = serviceRate;
            this.capacity = capacity;
        }

        /** Creates a new instance of ErlangC assuming an infinite queue capacity.
         @param arrivalRate the arrival rate.
         @param serviceRate the service rate.
         */
        public ErlangC(double arrivalRate, double serviceRate) {
            if (arrivalRate < 0 || serviceRate < 0)
                throw new IllegalArgumentException("The arguments cannot be negative!");

            this.arrivalRate = arrivalRate;
            this.serviceRate = serviceRate;
            this.capacity = Integer.MAX_VALUE;
        }

        /**
         * Returns the delay probability : $Pr\{W > 0\}$, such that the call will wait.
         @param server the number of servers.
         @return the delay probability.
         */
        public double getProbDelay(int server) {
            if (capacity == Integer.MAX_VALUE)
                return getProbDelay(arrivalRate, serviceRate, server);
            else
                return getProbDelay(arrivalRate, serviceRate, capacity, server);
        }

        /**
         * Returns the delay probability : $Pr\{W > 0\}$, such that the call will wait.
         * Assumes an infinite queue.
         @param arrivalRate the arrival rate.
         @param serviceRate the service rate.
         @param server the number of servers.
         @return the delay probability.
         */
        public static double getProbDelay(double arrivalRate, double serviceRate, int server) {
            if (arrivalRate < 0 || serviceRate < 0 || server < 0)
                throw new IllegalArgumentException("The parameters cannot be negative!");

            if (arrivalRate == 0)
                return 0;
            if (serviceRate == 0)
                return 1;
            if (server == 0)
                return 1;

            double load = arrivalRate / serviceRate;
            if (load >= server) // unstable
                return 1;

            double beta = server / load;
            double sumBeta = beta;

            for (int i = 1; i < server; i++) {
                beta = beta * (server - i) / load;
                sumBeta = sumBeta + beta;
            }
            return 1.0 / (1.0 + (1.0 - load / server) * sumBeta);
        }


        /**
         * Returns the delay probability : $Pr\{W > 0\}$, such that the call will wait.
         @param arrivalRate the arrival rate.
         @param serviceRate the service rate.
         @param capacity the capacity of the queue, sets to {@link Integer#MAX_VALUE} for
          * infinite queue capacity.
         @param server the number of servers.
         @return the delay probability.
         */
        public static double getProbDelay(double arrivalRate, double serviceRate, int capacity, int server) {
            if (arrivalRate < 0 || serviceRate < 0 || capacity < 0 || server < 0)
                throw new IllegalArgumentException("The parameters cannot be negative!");

            if (capacity == Integer.MAX_VALUE)
                return getProbDelay(arrivalRate, serviceRate, server);

            if (arrivalRate == 0)
                return 0;
            if (serviceRate == 0)
                return 1;
            if (server == 0)
                return 1;

            if (arrivalRate / serviceRate >= server) // unstable
                return 1;

            // Find pi0, the probability of state 0.
            // double pi0;

            double sumLoad = 0.0;
            double tempLoad = 1.0;

            int maxclient = server + capacity;

            for (int k = 1; k < server; k++) {
                tempLoad = tempLoad * arrivalRate / (k * serviceRate);
                sumLoad = sumLoad + tempLoad;
            }
            double t = sumLoad + 1.0;

            for (int k = server; k <= maxclient; k++) {
                tempLoad = tempLoad * arrivalRate / (server * serviceRate);
                if (tempLoad <= 0)
                    break;
                sumLoad = sumLoad + tempLoad;
            }
            sumLoad = sumLoad + 1.0;
            double pi0 = 1.0 / sumLoad;

            return 1.0 - pi0 * t;
        }


        /**
         * Returns the service level which is the proportion of calls that have waited less or equal to awt,
         * $Pr\{ W \le awt \}$. awt must be given in the same unit as the arrival and service rates.
         @param server the number of servers.
         @param awt the acceptable waiting time.
         @return the service level.
         */
        public double getServiceLevel(int server, double awt) {
            return getServiceLevel(arrivalRate, serviceRate, capacity, server, awt);
        }

        /**
         * Returns the service level which is the proportion of calls that have waited less or equal to awt,
         * $Pr\{ W \le awt \}$. awt must be given in the same unit as the arrival and service rates.
         * This method assumes a queue with an infinite capacity.
         @param arrivalRate the arrival rate.
         @param serviceRate the service rate.
         @param server the number of servers.
         @param awt the acceptable waiting time.
         @return the service level.
         */
        public static double getServiceLevel(double arrivalRate, double serviceRate, int server, double awt) {
            if (arrivalRate < 0 || serviceRate < 0 || server < 0 || awt < 0)
                throw new IllegalArgumentException("The parameters cannot be negative!");

            return Math.max(0, 1.0 - (getProbDelay(arrivalRate, serviceRate, server) /
                Math.exp(((double)server*serviceRate - arrivalRate)*awt)));
        }

        /**
         * Returns the service level which is the proportion of calls that have waited less or equal to awt,
         * $Pr\{ W \le awt \}$. awt must be given in the same unit as the arrival and service rates.
         * Give a capacity of {@link Integer#MAX_VALUE} for a queue with an infinite capacity.
         @param arrivalRate the arrival rate.
         @param serviceRate the service rate.
         @param capacity the capacity of the queue.
         @param server the number of servers.
         @param awt the acceptable waiting time.
         @return the service level.
         */
        public static double getServiceLevel(double arrivalRate, double serviceRate, int capacity,
                                             int server, double awt) {
            if (arrivalRate < 0 || serviceRate < 0 || capacity < 0 || server < 0 || awt < 0)
                throw new IllegalArgumentException("The parameters cannot be negative!");

            if (capacity == Integer.MAX_VALUE)
                return getServiceLevel(arrivalRate, serviceRate, server, awt);
            else
                return Math.max(0, 1.0 - (getProbDelay(arrivalRate, serviceRate, capacity, server) /
                    Math.exp(((double)server*serviceRate - arrivalRate)*awt)));
        }

        /**
         * Returns the minimum number $c$ of servers needed to have a service level of at least $sl$,
         * that is : $\min_{c \ge 0} \{ c : Pr\{ W \le awt\} \ge sl \}$.
         * This function uses a binary search.
         @param awt the acceptable waiting time.
         @param sl the target service level, it must be in the interval $[0, 1]$.
         @return the minimum number of servers needed to satisfy a service level of $sl$.
         */
        public int minServer(double awt, double sl) {
            if (capacity == Integer.MAX_VALUE)
                return minServer(arrivalRate, serviceRate, awt, sl);
            else
                return minServer(arrivalRate, serviceRate, capacity, awt, sl);
        }

        /**
         * Returns the minimum number $c$ of servers needed to have a service level of at least $sl$,
         * that is : $\min_{c \ge 0} \{ c : Pr\{ W \le awt\} \ge sl \}$.
         * The capacity of the queue is assumed infinite.
         * This function uses a binary search.
         @param arrivalRate the exponential arrival rate.
         @param serviceRate the exponential service rate.
         @param awt the acceptable waiting time.
         @param sl the target service level, it must be in the interval $[0, 1]$.
         @return the minimum number of servers needed to satisfy a service level of $sl$.
         */
        public static int minServer(double arrivalRate, double serviceRate,
                                    double awt, double sl) {
            if (arrivalRate < 0 || serviceRate < 0 || awt < 0)
                throw new IllegalArgumentException("The parameters cannot be negative!");

            if (sl < 0 || sl > 1)
                throw new IllegalArgumentException("The target service level must be in $[0, 1]$.");

            if (arrivalRate == 0) // if no calls
                return 0;
            if (serviceRate == 0) // no service
                return Integer.MAX_VALUE;

            if (getServiceLevel(arrivalRate, serviceRate, 1, awt) >= sl)
                return 1;

            double load = arrivalRate / serviceRate;
            double s;

            // initialize the binary search
            int n1 = (int)Math.floor(load);
            int n2 = (int)Math.ceil(load + Math.sqrt(load));
            while (getServiceLevel(arrivalRate, serviceRate, n2, awt) < sl) {
                n1 = n2;
                n2 = (int)Math.max(n2+1, n2 + Math.sqrt(load));
            }

            // do binary search
            int n = 1;
            while(n2 - n1 > 1) {
                n = (int)Math.round((n2 + n1) / 2);
                s = getServiceLevel(arrivalRate, serviceRate, n, awt);
                // System.out.println("n : " + n + "\t sl : " + s + "\t n1 : " + n1 + "\t n2 : " + n2);
                if (s >= sl)
                    n2 = n;
                else
                    n1 = n;
            }
            return n2;
        }

        /**
         * Returns the minimum number $c$ of servers needed to have a service level of at least $sl$,
         * that is : $\min_{c \ge 0} \{ c : Pr\{ W \le awt\} \ge sl \}$.
         * If the capacity is {@link Integer#MAX_VALUE}, the capacity of the queue
         * is assumed infinite.
         * This function uses a binary search.
         @param arrivalRate the exponential arrival rate.
         @param serviceRate the exponential service rate.
         @param capacity the capacity of the queue.
         @param awt the acceptable waiting time.
         @param sl the target service level, it must be in the interval $[0, 1]$.
         @return the minimum number of servers needed to satisfy a service level of $sl$.
         */
        public static int minServer(double arrivalRate, double serviceRate,
                                    int capacity, double awt, double sl) {

            if (arrivalRate < 0 || serviceRate < 0 || capacity < 0 || awt < 0)
                throw new IllegalArgumentException("The parameters cannot be negative!");

            if (capacity == Integer.MAX_VALUE) // if infinite queue capacity
                return minServer(arrivalRate, serviceRate, awt, sl);

            if (sl < 0 || sl > 1)
                throw new IllegalArgumentException("The target service level must be in $[0, 1]$.");

            if (arrivalRate == 0) // if no calls
                return 0;
            if (serviceRate == 0) // no service
                return Integer.MAX_VALUE;

            if (getServiceLevel(arrivalRate, serviceRate, capacity, 1, awt) >= sl)
                return 1;

            double load = arrivalRate / serviceRate;
            double s;

            // initialize the binary search
            int n1 = (int)Math.floor(load);
            int n2 = (int)Math.ceil(load + Math.sqrt(load));
            while (getServiceLevel(arrivalRate, serviceRate, capacity, n2, awt) < sl) {
                n1 = n2;
                n2 = (int)Math.max(n2+1, n2 + Math.sqrt(load));
            }

            // do binary search
            int n = 1;
            while(n2 - n1 > 1) {
                n = (int)Math.round((n2 + n1) / 2);
                s = getServiceLevel(arrivalRate, serviceRate, capacity, n, awt);
                // System.out.println("n : " + n + "\t sl : " + s + "\t n1 : " + n1 + "\t n2 : " + n2);
                if (s >= sl)
                    n2 = n;
                else
                    n1 = n;
            }
            return n2;
        }

        /**
         * Returns the average wait time : $\mathbb{E}[W]$.
         @param server the number of servers.
         @return the average wait time.
         */
        public double getAverageWaitTime(int server){
            return getAverageWaitTime(arrivalRate, serviceRate, capacity, server);
        }

        /**
         * Returns the average wait time : $\mathbb{E}[W]$. It assumes an infinite queue capacity.
         @param arrivalRate the arrival rate.
         @param serviceRate the service rate.
         @param server the number of servers.
         @return the average wait time.
         */
        public static double getAverageWaitTime(double arrivalRate, double serviceRate, int server) {
            return getAverageWaitTime(arrivalRate, serviceRate, Integer.MAX_VALUE, server);
        }

        /**
         * Returns the average wait time : $\mathbb{E}[W]$.
         @param arrivalRate the arrival rate.
         @param serviceRate the service rate.
         @param capacity the capacity of the queue.
         @param server the number of servers.
         @return the average wait time.
         */
        public static double getAverageWaitTime(double arrivalRate, double serviceRate,
                                                int capacity, int server) {

            if (arrivalRate < 0 || serviceRate < 0 || capacity < 0 || server < 0)
                throw new IllegalArgumentException("The parameters cannot be negative!");

            // if the system is unstable
            if (arrivalRate >= serviceRate * server)
                return Double.POSITIVE_INFINITY;

            return getProbDelay(arrivalRate, serviceRate, capacity, server) / (serviceRate * server - arrivalRate);
        }

        /**
         * Returns the average excess time : $\mathbb{E}[(W - awt)^{+}]$. It corresponds
         * to the average of waiting time exceeding $awt$.
         @param server the number of servers.
         @param awt the acceptable waiting time.
         @return the average excess time.
         */
        public double getAverageExcessTime(int server, double awt) {
            return getAverageExcessTime(arrivalRate, serviceRate, capacity, server, awt);
        }

        /**
         * Returns the average excess time : $\mathbb{E}[(W - awt)^{+}]$. It corresponds
         * to the average of waiting time exceeding $awt$. It assumes an infinite queue
         * capacity.
         @param arrivalRate the arrival rate.
         @param serviceRate the service rate.
         @param server the number of servers.
         @param awt the acceptable waiting time.
         @return the average excess time.
         */
        public static double getAverageExcessTime(double arrivalRate, double serviceRate,
                                                  int server, double awt) {
            return getAverageExcessTime(arrivalRate, serviceRate, Integer.MAX_VALUE, server, awt);
        }

        /**
         * Returns the average excess time : $\mathbb{E}[(W - awt)^{+}]$. It corresponds
         * to the average of waiting time exceeding $awt$.
         @param arrivalRate the arrival rate.
         @param serviceRate the service rate.
         @param capacity the capacity of the queue.
         @param server the number of servers.
         @param awt the acceptable waiting time.
         @return the average excess time.
         */
        public static double getAverageExcessTime(double arrivalRate, double serviceRate, int capacity,
                                                  int server, double awt) {

            if (arrivalRate < 0 || serviceRate < 0 || capacity < 0 || server < 0 || awt < 0)
                throw new IllegalArgumentException("The parameters cannot be negative!");

            // if the system is unstable
            if (arrivalRate >= serviceRate * server)
                return Double.POSITIVE_INFINITY;

            return getProbDelay(arrivalRate, serviceRate, capacity, server) /
                Math.exp(serviceRate * server * awt - arrivalRate * awt)  /
                (serviceRate * server - arrivalRate);
        }


        /**
         * Returns the service level and the delay probability of given parameters.
         * Arguments to give : <arrival rate> <service rate> <number of servers> <awt> [<capacity>].
         * If the capacity is omitted, the queue is assumed to have an infinite capacity.
         */
        public static void main(String args[]) throws Exception {

            if (args.length < 4) {
                System.out.println("Must enter : <arrival rate> <service rate> <number of servers> <awt> [<capacity>]");
                System.exit(-1);
            }

            double arrival = Double.parseDouble(args[0]);
            double service = Double.parseDouble(args[1]);
            int server = Integer.parseInt(args[2]);
            double awt = Double.parseDouble(args[3]);
            int capacity = -1;

            if (args.length > 4) {
                capacity = Integer.parseInt(args[4]);
            }

            ErlangC c;

            if (args.length == 4)
                c = new ErlangC(arrival, service);
            else
                c = new ErlangC(arrival, service, capacity);

            System.out.println("Delay prob : " + c.getProbDelay(server));
            System.out.println("SL : " + c.getServiceLevel(server, awt));
            System.out.println("Average wait time : " + c.getAverageWaitTime(server));
            System.out.println("Average excess time : " + c.getAverageExcessTime(server, awt));
        }

    }



