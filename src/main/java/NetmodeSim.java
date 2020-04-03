import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import lpsolve.LpSolveException;
import org.apache.commons.lang3.ArrayUtils;
import org.apache.commons.math3.distribution.PoissonDistribution;
import org.cloudbus.cloudsim.allocationpolicies.VmAllocationPolicySimple;
import org.cloudbus.cloudsim.cloudlets.Cloudlet;
import org.cloudbus.cloudsim.core.CloudSim;
import org.cloudbus.cloudsim.datacenters.Datacenter;
import org.cloudbus.cloudsim.datacenters.DatacenterSimple;
import org.cloudbus.cloudsim.hosts.Host;
import org.cloudbus.cloudsim.hosts.HostSimple;
import org.cloudbus.cloudsim.provisioners.ResourceProvisioner;
import org.cloudbus.cloudsim.provisioners.ResourceProvisionerSimple;
import org.cloudbus.cloudsim.resources.Pe;
import org.cloudbus.cloudsim.resources.PeSimple;
import org.cloudbus.cloudsim.schedulers.vm.VmScheduler;
import org.cloudbus.cloudsim.schedulers.vm.VmSchedulerTimeShared;
import org.cloudbus.cloudsim.utilizationmodels.UtilizationModel;
import org.cloudbus.cloudsim.utilizationmodels.UtilizationModelDynamic;
import org.cloudbus.cloudsim.vms.Vm;
import org.cloudbus.cloudsim.vms.VmSimple;
import org.cloudsimplus.builders.tables.CloudletsTableBuilder;
import org.cloudsimplus.listeners.EventInfo;

import java.util.*;
import java.util.List;
import java.util.stream.IntStream;

public class NetmodeSim {
    // TODO: read these values from external file
    // TODO: set debugging toggle and different colors
    // TODO: do not use constants directly in methods; add them to method call

    // Simulation related constants
    private static final double TIME_TO_TERMINATE_SIMULATION = 61;
    private static final double SCHEDULING_INTERVAL = 1;
    private static final int SAMPLING_INTERVAL = 30;

    // n-MMC related constants
    private static final Boolean CREATE_NMMC_TRANSITION_MATRIX = false;
    private static final int NMMC_HISTORY = 2;

    // Environment related constants
    private static final int POI = 9; //define points of interest
    private static final int APPS = 2;
    private static final int GROUPS = 20;
    private static final int GROUP_SIZE = 4; // [1..4]
    private static final int GRID_SIZE = 3;

    // Edge Servers related constants
    private static final int EDGE_HOSTS = 3;
    private static final int EDGE_HOST_PES = 4;
    private static final int EDGE_HOST_PE_MIPS = 2000;
    private static final int EDGE_HOST_RAM = 64768;
    private static final int EDGE_HOST_BW = 1000000;

    // VM related constants
    private static final int[][] VM_PES = {{1, 2, 4}, {1, 2, 4}}; // [app][flavor]
    private static final int[][] VM_PE_MIPS = {{2000, 2000, 2000}, {2000, 2000, 2000}};
    private static final double[][] VM_GUARANTEED_AVG_RR = {{37.35, 82.24, 172.68}, {37.35, 82.24, 172.68}};
    private static final double[][] VM_GUARANTEED_MAX_RR = {{50.00, 110.00, 210.00}, {50.00, 110.00, 210.00}};
    private static final int VM_RAM = 4096;
    private static final int VM_BW = 200000;
    private static final double UNDERUTILISED_VM_CUTOFF = 0.5;

    // Task related constants
    private static final int TASK_PES = 1;
    private static final int TASK_LENGTH = 1000;
    private static final double[] APP_REQUEST_RATE_PER_USER = {3, 7}; // needed in order to make a sound translation
    private static final int[][] CELL_OFFLOADING_DISTANCE_INDEX = {{1, 1, 4}, {3, 1, 2}, {4, 4, 2}};

    // Various "global" variables
    private Double[][] simData;
    private int lastAccessed;
    private int maxVmSize;
    private final CloudSim simulation = new CloudSim();
    private DatacenterBrokerSimpleExtended[] edgeBroker;
    private ArrayList<Vm>[][] vmList;
    private ArrayList<TaskSimple>[][] taskList;
    private HashMap<Long, Double> accumulatedCpuUtil;
    private int [][] taskCounter;
    private int lastIntervalFinishTime;
    private HashMap<String, int[]> transitionsLog;
    private HashMap<String, double[]> transitionProbabilitiesMap;
    private double[][][] requestRatePerCell;
    private Boolean firstEvent;
    private CSVmachine csvm;
    private Group[] groups;
    private ArrayList<int[][]> feasibleFormations;
    private double[][] guaranteedWorkload;
    private double[] energyConsumption;
    private LoadBalancer[] loadBalancer;
    ArrayList<Vm>[] vmPool;

    //TODO ds initilizations
    ArrayList <Vm>[] staticVmList;
    double[][] ArrivalRateLB;
    //Algorithm settings
    private double D=1000000000;
    private double d= 0.11;                            // parameter for |D|<d
    private double e= 0.1;                            // e parameter for accuracy parameter
    private double u= 0.1;                             // theta parameter for accuracy
    //default structure of cloudsimplus
    private double [] Ti = new double [POI];
    private int[] OverloadedCloudlets = new int[POI];
    private int[] UnderloadedCloudlets = new int[POI];
    //TODO ds find these values
    double[] ServiceRate = {400,200,300,500,405,675,349,348,157f};
    double[] NumberofServers = {2,4,3,4,5,4,5,4,3};
    double [][] predictedWorkloadStatic = {{100, 100}, {50, 50}, {70, 70}, {100, 100}, {50, 50}, {70, 70}, {100, 100}, {50, 50}, {70, 70}};
    private double [] fi = new double [POI];
    private double [] fj = new double [POI];
    private double[] lj = new double[POI];  // synolikh roh poy mpenei se kathe underloaded
    private double[] li = new double[POI];
    //private double[] ArrivalRate = new double[POI];
    private double Dtotal;
    private double[][] AverageResponseTimeTi = new double[POI][32000]; // HTAN 4000
    private static double[][] NetDelay ={{0.000000,0.174351,0.151792,0.102222,0.121226,0.167159,0.136996,0.151449,0.137782},
            {0.174351,0.000000,0.104213,0.118699,0.187412,0.197028,0.168254,0.144612,0.177855},
            {0.151792,0.104213,0.000000,0.182387,0.133270,0.132010,0.192918,0.146808,0.122887},
            {0.102222,0.118699,0.182387,0.000000,0.189572,0.102149,0.114024,0.154943,0.114506},
            {0.121226,0.187412,0.133270,0.189572,0.000000,0.136235,0.108649,0.182796,0.126507},
            {0.167159,0.197028,0.132010,0.102149,0.136235,0.000000,0.167916,0.115575,0.131254},
            {0.136996,0.168254,0.192918,0.114024,0.108649,0.167916,0.000000,0.191353,0.105500},
            {0.151449,0.144612,0.146808,0.154943,0.182796,0.115575,0.191353,0.000000,0.174703},
            {0.137782,0.177855,0.122887,0.114506,0.126507,0.131254,0.105500,0.174703,0.000000}};


    public static void main(String[] args) {
        new NetmodeSim();
    }

    public NetmodeSim() {
        csvm = new CSVmachine(POI, APPS, SAMPLING_INTERVAL);

        transitionsLog = new HashMap<>();
        accumulatedCpuUtil = new HashMap<>();
        vmList = (ArrayList<Vm>[][]) new ArrayList[2*POI][APPS];
        taskList = (ArrayList<TaskSimple>[][]) new ArrayList[2*POI][APPS];
        taskCounter = new int[2*POI][APPS];

        simData = csvm.readSimCSVData();
        firstEvent = true;

        // Create groups with random starting position
        createGroups(GROUPS, GROUP_SIZE, APPS, GRID_SIZE);

        // Add one broker and one datacenter per Point of Interest
        createBrokersAndDatacenters(2*POI);

        // Initialize transition probabilities to use for group movement prediction (mobility)
        if (!CREATE_NMMC_TRANSITION_MATRIX) {
            transitionProbabilitiesMap = csvm.readNMMCTransitionMatrixCSV();
//            System.out.println("Transition Probabilities Map: ");
//            transitionProbabilitiesMap.entrySet().forEach(entry -> {
//                System.out.println(entry.getKey() + " -> " + Arrays.toString(entry.getValue()));
//            });
        }

        //TODO ds translate number of servers and serviceRate per server to static placement
        //TODO ds perform static placement of vms and hosts for POI 9 -> 18
        //TODO ds service rate number of servers per app
        //TODO define network delay matrix and upper value of arrival rate!!
        for (int i = 0; i < POI; i++) {
            for (int j=0; (j < 32000); j++)                      //htan 4000
                CalculationofAverageResponseTime( (double)j/100, ServiceRate[i], (int)NumberofServers[i], i);
        }
        //TODO (DONE) ds calculate offline averageResponseTime
        //TODO (DONE) ds after the estimation of workload load balance it between cloudlets
        //TODO (DONE) ds call for each time the algorithm per app! feed the algorithm with the placement for each app and the workload for each app

        feasibleFormations = calculateFeasibleServerFormations(EDGE_HOST_PES, VM_PES);
        guaranteedWorkload = calculateServerGuaranteedWorkload(feasibleFormations);
        energyConsumption = calculateServerPowerConsumption(feasibleFormations, EDGE_HOST_PES);
        ArrayList<Integer>[] vmPlacementStatic =
                optimizeVmPlacement(EDGE_HOSTS, predictedWorkloadStatic, EDGE_HOST_PES, UNDERUTILISED_VM_CUTOFF);
        staticVmList = spawnStaticVms(feasibleFormations, vmPlacementStatic);

        // Calculate variables required for VM optimization
        feasibleFormations = calculateFeasibleServerFormations(EDGE_HOST_PES, VM_PES);
        guaranteedWorkload = calculateServerGuaranteedWorkload(feasibleFormations);
        energyConsumption = calculateServerPowerConsumption(feasibleFormations, EDGE_HOST_PES);

        // Initial Predicted Workload TODO: change
        double [][] predictedWorkload = {{100, 100}, {50, 50}, {70, 70}, {100, 100}, {50, 50}, {70, 70}, {100, 100},
                {50, 50}, {70, 70}};
        ArrayList<Integer>[] vmPlacement =
                optimizeVmPlacement(EDGE_HOSTS, predictedWorkload, EDGE_HOST_PES, UNDERUTILISED_VM_CUTOFF);

        // Create number of initial VMs for each app
        spawnVms(feasibleFormations, vmPlacement);

        // Run simulation
        runSimulationAndPrintResults();

        System.out.println(getClass().getSimpleName() + " finished!");

        // Create a document containing the transitions' Log
        if (CREATE_NMMC_TRANSITION_MATRIX) csvm.createNMMCTransitionMatrixCSV(transitionsLog);
    }

    // Take decisions with a second-wise granularity
    private void masterOfPuppets(final EventInfo evt) {
        // Make sure to call only once per second
        if (!(lastAccessed == (int) evt.getTime())) {
            // If a full interval has been completed or first interval, predict group movement, optimize vm placement,
            // actually move group, generate request rate per cell
            if (((int) evt.getTime() % SAMPLING_INTERVAL == 0) || firstEvent) {

                if (!firstEvent) {
                    // Collect Stats and present them
                    IntervalStats stats = collectTaskStats();
                    int[][] intervalFinishedTasks = stats.getIntervalFinishedTasks();
                    int[][] intervalAdmittedTasks = stats.getIntervalAdmittedTasks();
                    double[][] accumulatedResponseTime = stats.getAccumulatedResponseTime();

                    // TODO: remove when debugging is over
                    System.out.println("Request Rate to generate in Previous Interval: " + Arrays.deepToString(requestRatePerCell));

                    csvm.formatAndPrintIntervalStats(intervalFinishedTasks, intervalAdmittedTasks,
                            accumulatedResponseTime, accumulatedCpuUtil);

                    // Initiate interval variables
                    accumulatedCpuUtil = new HashMap<>();
                    lastIntervalFinishTime = (int) evt.getTime();
                }

                // Predict group movement and random users arrival //
                int[][] predictedUsersPerCellPerApp = predictNextIntervalUsers(groups, transitionProbabilitiesMap);

                // Translate predicted users per cell to workload
                double[][] predictedWorkload =
                        predictNextIntervalWorkload(predictedUsersPerCellPerApp, APP_REQUEST_RATE_PER_USER);

                // Optimize VM placement based on energy consumption and guaranteed workload completion,
                // actually allocate VMs and perform MRF
                ArrayList<Integer>[] vmPlacement =
                        optimizeVmPlacement(EDGE_HOSTS, predictedWorkload, EDGE_HOST_PES, UNDERUTILISED_VM_CUTOFF);
                double[][] residualWorkload = calculateResidualWorkload(vmPlacement, guaranteedWorkload, predictedWorkload);
                int[] residualResources = calculateResidualResources(vmPlacement, EDGE_HOSTS);

                // MRF step (TODO)

                // Spawn VMs realizing the above decisions
                vmPool = spawnVms(feasibleFormations, vmPlacement);

                // Create Load Balancers and assign them one per POI
                createLoadBalancers(vmPool);

                // Move groups
                for (Group group : groups)
                    group.move(transitionsLog, POI);

                // Change request rate based on the groups movement
                requestRatePerCell = createRequestRate(createUsers(GRID_SIZE, groups),
                        APP_REQUEST_RATE_PER_USER, predictedWorkload);

                //TODO (DONE) ds load balancing before that! predicted workload is the next arrival rate per poi per app.
                double [][] NextArrivalRate = new double [POI][APPS];
                for (int app = 0; app < APPS; app++) {
                    double [] AppArrivalRate = new double [POI];
                    AppArrivalRate = Algorithm1(ServiceRate, NumberofServers,predictedWorkload,app);
                    for (int poi = 0; poi < POI; poi++){
                        NextArrivalRate[poi][app] = AppArrivalRate[poi];
                    }
                }
                ArrivalRateLB = NextArrivalRate;

                // First interval arrangements are now over
                if (firstEvent) firstEvent = false;
            }

            // Actually create the requests based on the previously generated request rate and delegate them per VM/app
            if (!CREATE_NMMC_TRANSITION_MATRIX) generateRequests(requestRatePerCell, ArrivalRateLB, evt);

            // Vm resource usage stats collected per second
            collectVmStats();

            lastAccessed = (int) evt.getTime();
        }
    }

    private int[][] predictNextIntervalUsers(Group[] groups, HashMap<String, double[]> transitionProbabilitiesMap) {
        double[] transitionProbabilities;
        double[][] floatPredictedUsersPerCellPerApp = new double[POI][APPS];
        int[][] predictedUsersPerCellPerApp = new int[POI][APPS];

        for (Group group : groups) {
            transitionProbabilities = transitionProbabilitiesMap.get(group.historicState);
            if (transitionProbabilities == null) {
                transitionProbabilities = new double[POI];
                for (int i = 0; i < POI; i++)
                    transitionProbabilities[i] = 1.0 / POI;
            }
//            System.out.println("Historic state: " + group.historicState);
//            System.out.println("Transition Probabilites: " + Arrays.toString(transitionProbabilities));
//            System.out.println("Group Size: " + group.size);
            for (int i = 0; i < transitionProbabilities.length; i++) {
                // TODO maybe add +1 to predicted users
                floatPredictedUsersPerCellPerApp[i][group.app] += group.size * transitionProbabilities[i];
//                System.out.println("POI " + i + " Group Predicted Users: " + group.size * transitionProbabilities[i]);
//                System.out.println("POI " + i + " Total Predicted Users: " + floatPredictedUsersPerCellPerApp[i][group.app]);
            }
        }
//        System.out.println("Total Predicted Users: " + Arrays.deepToString(floatPredictedUsersPerCellPerApp));
        for (int i = 0; i < POI; i++)
            for (int j = 0; j < APPS; j++)
                predictedUsersPerCellPerApp[i][j] = (int)Math.round(floatPredictedUsersPerCellPerApp[i][j]);
//        System.out.println("Total Predicted Users: " + Arrays.deepToString(predictedUsersPerCellPerApp));

        return predictedUsersPerCellPerApp;
    }

    private double[][] predictNextIntervalWorkload(int[][] predictedUsersPerCellPerApp, double[] appRequestRatePerUser) {
        double[][] predictedIntervalWorkload = new double[POI][APPS];
        int dataRow, dataCol;

        for (int i = 0; i < predictedUsersPerCellPerApp.length; i++) {
            for (int app = 0; app < APPS; app++) {
                int distance = CELL_OFFLOADING_DISTANCE_INDEX[i / GRID_SIZE][i % GRID_SIZE];
                if (predictedUsersPerCellPerApp[i][app] != 0) {
                    dataRow = (predictedUsersPerCellPerApp[i][app] * distance) - 1;
//                    System.out.println("SimData rows: " + simData.length);
                    if (dataRow > simData.length) dataRow = simData.length - 1;
                    dataCol = 12; // TODO: fixed at column 12. Make it Variable
                    predictedIntervalWorkload[i][app] =
                            Math.round(simData[dataRow][dataCol] * appRequestRatePerUser[app] * 100.0) / 100.0;
                }
                else
                    predictedIntervalWorkload[i][app] = 0;
            }
        }

        System.out.println("Total Predicted Workload: " + Arrays.deepToString(predictedIntervalWorkload));
        return predictedIntervalWorkload;
    }

    private double[][] calculateResidualWorkload(ArrayList<Integer>[] vmPlacement, double[][] guaranteedWorkload,
                                                 double[][] predictedWorkload) {
        double[][] residualWorkload = new double[POI][APPS];

        for (int poi = 0; poi < POI; poi++) {
            double[] servedWorkload = new double[APPS];
            for (int vmFormation : vmPlacement[poi]) {
                for (int app = 0; app < APPS; app++) {
                    servedWorkload[app] += guaranteedWorkload[vmFormation][app];
                }
            }
            for (int app = 0; app < APPS; app++) {
                if (servedWorkload[app] - predictedWorkload[poi][app] > 0)
                    residualWorkload[poi][app] = 0;
                else
                    residualWorkload[poi][app] = predictedWorkload[poi][app] - servedWorkload[app];
            }
//            System.out.println("Served Workload" + Arrays.toString(servedWorkload));
//            System.out.println("Predicted Workload" + Arrays.toString(predictedWorkload[poi]));
//            System.out.println("Residual Workload" + Arrays.toString(residualWorkload[poi]));
        }

        System.out.println("Total Residual Workload: " + Arrays.deepToString(residualWorkload));
        return residualWorkload;
    }

    private int[] calculateResidualResources(ArrayList<Integer>[] vmPlacement, int numberOfHosts) {
        int[] residualResources = new int[POI];

        int poi = 0;
        for (ArrayList<Integer> site : vmPlacement) {
            residualResources[poi] = numberOfHosts - site.size();
            poi++;
        }

        System.out.println("Total Residual Resources: " + Arrays.toString(residualResources));
        return residualResources;
    }

    private ArrayList<Integer>[] optimizeVmPlacement(int hosts, double[][] predictedWorkload, int edgeHostPes,
                                                     double cutOffPoint) {
        ArrayList<Integer>[] tempVmPlacement = new ArrayList[POI];
        ArrayList<Integer>[] vmPlacement = new ArrayList[POI];

        // Solve lp optimization
        for (int poi = 0; poi < POI; poi++) {
//            System.out.println(Arrays.deepToString(guaranteedWorkload));
//            System.out.println(Arrays.toString(energyConsumption));
            try {
                System.out.print("POI: " + poi + ", ");
                tempVmPlacement[poi] =
                        Optimizer.optimizeVmPlacement(guaranteedWorkload, energyConsumption, hosts, predictedWorkload[poi]);
            } catch (LpSolveException e) {
                e.printStackTrace();
            }
        }
        System.out.println("\nVM Placement (before rejecting underutilised servers): \n"
                + Arrays.deepToString(tempVmPlacement));

        // Cut out "underutilised" servers. Underutilisation criteria = less than 50% of the cores allocated
        int poi = 0;
        for (ArrayList<Integer> tempSite : tempVmPlacement) {
            ArrayList<Integer> site = new ArrayList<>(tempSite);
            for (int server : tempSite) {
                int serverCoreSum = 0;
                for (int app = 0; app < APPS; app++)
                    serverCoreSum += IntStream.of(feasibleFormations.get(server)[app]).sum();
//                System.out.println(serverCoreSum);
                // throws java.util.ConcurrentModificationException if modifying the iterated array. Thus use tempSite
                if ((serverCoreSum / (double) edgeHostPes) <= cutOffPoint) site.remove(server);
            }
            vmPlacement[poi] = site;
            poi++;
        }
        System.out.println("VM Placement (final): \n" + Arrays.deepToString(vmPlacement));

        return vmPlacement;
    }

    private double[][] calculateServerGuaranteedWorkload(ArrayList<int[][]> feasibleFormations) {
        int totalFormations = feasibleFormations.size();
        double[][] guaranteedWorkload = new double[totalFormations][APPS];

        for (int permutation = 0; permutation < totalFormations; permutation++) {
//            System.out.println(Arrays.deepToString(feasibleFormations.get(permutation)));
            for (int app = 0; app < APPS; app++) {
                for (int flavor : feasibleFormations.get(permutation)[app]) {
                    guaranteedWorkload[permutation][app] += VM_GUARANTEED_AVG_RR[app][ArrayUtils.indexOf(VM_PES[app], flavor)];
                }
            }
        }

        System.out.println("Server Formations Guaranteed Workload: " + Arrays.deepToString(guaranteedWorkload));

        return guaranteedWorkload;
    }

    private double[] calculateServerPowerConsumption(ArrayList<int[][]> feasibleFormations, int serverCores) {
        int totalFormations = feasibleFormations.size();
        double[] energyConsumption = new double[feasibleFormations.size()];
        double pMax = 2000; // the maximum power consumed when the server is fully utilized, in Watts
        double k = 0.6; // k is the fraction of power consumed by an idle server (usually around 70%)

        for (int permutation = 0; permutation < totalFormations; permutation++) {
//            System.out.println(Arrays.deepToString(feasibleFormations.get(permutation)));
            for (int app = 0; app < APPS; app++) {
                for (int flavorCores : feasibleFormations.get(permutation)[app]) {
//                    System.out.println(flavorCores);
//                    System.out.println(ArrayUtils.indexOf(VM_PES[app], flavorCores));
                    // Use Energy Model defined in paper to predict the power consumed by each VM provisioned
                    // in a server with an error below 5%
                    energyConsumption[permutation] +=
                            calculateVmPowerConsumption(serverCores, ArrayUtils.indexOf(VM_PES[app], flavorCores), k, pMax);
//                    System.out.println(energyConsumption[permutation]);
                }
            }
        }

        System.out.println("Server Formations Power Consumption: " + Arrays.toString(energyConsumption));

        return energyConsumption;
    }

    private double calculateVmPowerConsumption(int serverCores, int vmCores, double k, double pMax) {
        return k * pMax + ((1 - k) * pMax * vmCores / serverCores);
    }

    private ArrayList<int[][]> calculateFeasibleServerFormations(int serverCores, int[][] flavorCores) {
        ArrayList<int[][]> formations = new ArrayList<>();
        ArrayList<int[]> tempFormations = new ArrayList<>();
        ArrayList<int[][]> uniqueFormations = new ArrayList<>();

        // Get permutations per App
        for (int length = 1; length <= serverCores; length++) {
            for (int app = 0; app < APPS; app++) {
                for (int[] permutation : Permutator.calculatePermutationsOfLength(flavorCores[app], length)) {
                    // First Check
                    if (IntStream.of(permutation).sum() <= serverCores) tempFormations.add(permutation);
                }
            }
        }

        // Get total feasible permutations
        for (int[][] permutation : Permutator.calculatePermutationsOfLength(tempFormations, APPS)) {
            int permutationCoreSum = 0;
            for (int app = 0; app < APPS; app++) permutationCoreSum += IntStream.of(permutation[app]).sum();
            if (permutationCoreSum <= serverCores) formations.add(permutation);
        }

        // Remove duplicates
        for (int[][] newPermutation : formations) {
            // Sort flavors inside
            for (int[] appWisePermutation : newPermutation) Arrays.sort(appWisePermutation);
            boolean unique = true;
            for (int[][] oldPermutation : uniqueFormations) {
                // Sort flavors inside
                for (int[] appWisePermutation : oldPermutation) Arrays.sort(appWisePermutation);
                if (Arrays.deepEquals(newPermutation, oldPermutation)) unique = false;
            }
            if (unique)
                uniqueFormations.add(newPermutation);
        }

        for (int[][] permutation : uniqueFormations) {
            int permutationCoreSum = 0;
            for (int app = 0; app < APPS; app++) permutationCoreSum += IntStream.of(permutation[app]).sum();
//            System.out.println(permutationCoreSum);
//            System.out.println(Arrays.deepToString(permutation));
        }

        return uniqueFormations;
    }

    private void collectVmStats() {
        for (int poi = 0; poi < 2* POI; poi++) {
            for (int app = 0; app < APPS; app++) {
                for (Vm vm : loadBalancer[poi].vmsOfApp[app]) {
                    if (accumulatedCpuUtil.containsKey(vm.getId()))
                        accumulatedCpuUtil.put(vm.getId(),
                                accumulatedCpuUtil.get(vm.getId()) + vm.getCpuPercentUtilization());
                    else
                        accumulatedCpuUtil.put(vm.getId(), vm.getCpuPercentUtilization());
                    //System.out.println("VM ID: " + vm.getId());
                    //System.out.println("Current CPU Util: " + vm.getCpuPercentUtilization());
                    //System.out.println("Total CPU Util: " + accumulatedCpuUtil.get(vm.getId()));
                }
            }
        }
    }

    private IntervalStats collectTaskStats() {
        int[][] intervalFinishedTasks = new int[2*POI][APPS];
        int[][] intervalAdmittedTasks = new int[2*POI][APPS];
        double[][] accumulatedResponseTime  = new double[2*POI][APPS];

        for (int poi = 0; poi < 2*POI; poi++) {
//                System.out.println(edgeBroker[poi].getCloudletFinishedList().size());
            for (Cloudlet c : edgeBroker[poi].getCloudletFinishedList()) {
                // Ensure that Task has been completed within the Interval
                if (c.getFinishTime() > lastIntervalFinishTime) {
//                        System.out.println("Task ID: " + c.getId());
//                        System.out.println("Execution Time: " + c.getActualCpuTime());
//                        System.out.println("Finish Time: " + c.getFinishTime());
//                        System.out.println("Start Time: " + c.getExecStartTime());
//                        System.out.println("-------------------------------------");
                    JsonObject description = new JsonParser().parse(c.getVm().getDescription()).getAsJsonObject();
                    int app = description.get("App").getAsInt();
                    intervalFinishedTasks[poi][app]++;
                    accumulatedResponseTime[poi][app] += c.getActualCpuTime();
//                    System.out.println("Current accumulated Response Time: " + accumulatedResponseTime[poi][app]);
//                    System.out.println(" + " + (c.getFinishTime() - c.getExecStartTime()));
//                    System.out.println(" ------------------------------------------");
                }
            }
        }

        for (int poi = 0; poi < 2*POI; poi++) {
//               System.out.println(edgeBroker[poi].getCloudletFinishedList().size());
//            System.out.println(edgeBroker[poi].getCloudletSubmittedList().size());
            for (Cloudlet c : edgeBroker[poi].getCloudletSubmittedList()) {
                // Ensure that Task has been completed within the Interval
//                System.out.println(c.getLastDatacenterArrivalTime());
//                System.out.println(lastIntervalFinishTime);
                if (c.getLastDatacenterArrivalTime() > lastIntervalFinishTime) {
//                    System.out.println("VM description: " + c.getVm().getDescription());
                    JsonObject description = new JsonParser().parse(c.getVm().getDescription()).getAsJsonObject();
                    int app = description.get("App").getAsInt();
//                    System.out.println(c.getLastDatacenterArrivalTime());
                    intervalAdmittedTasks[poi][app]++;
//                    System.out.println(intervalAdmittedTasks[poi][app]);
                }
            }
        }

        return new IntervalStats(intervalFinishedTasks, intervalAdmittedTasks, accumulatedResponseTime);
    }

    private void correctlySetVmDescriptions(ArrayList<Vm> vmList) {
//        for (int poi = 0; poi < POI; poi++) {
//            for (int app = 0; app < APPS; app++) {
//                for (int vmi = 0; vmi < vmList.size(); vmi++) {
//                    Vm vm = vmList.get(vmi);
//                    vm.setDescription("{\"App\": " + app + " }"); // Vm Description in Json format
//                }
//            }
//        }
        for (Vm vm: vmList)
            vm.setDescription("{\"App\": " + vm.getId()%1000%100/10 + " }"); // Vm Description in Json format
    }

    // TODO: reconsider according to https://preshing.com/20111007/how-to-generate-random-timings-for-a-poisson-process/
    private void generateRequests(double[][][] requestRatePerCellPerApp, double[][] arrivalRateLB, EventInfo evt) {
        PoissonDistribution pD;
        PoissonDistribution pDLB;
        int tasksToCreateLB;
        int tasksToCreate;

        for (int i = 0; i < GRID_SIZE; i++) {
            for (int j = 0; j < GRID_SIZE; j++) {
                int poi = GRID_SIZE * i + j;
                for (int app = 0; app < APPS; app++) {
                    if (requestRatePerCellPerApp[i][j][app] != 0) {
                        pD = new PoissonDistribution(requestRatePerCell[i][j][app] / SAMPLING_INTERVAL);
                        tasksToCreate = pD.sample();
                        taskList[9+poi][app] = new ArrayList<>();
                        System.out.printf("%n#-----> Creating %d Task(s) at PoI %d, for App %d at time %.0f sec.%n",
                                tasksToCreate, poi, app, evt.getTime());
                        taskList[poi][app] = (ArrayList<TaskSimple>) createTasks(tasksToCreate, poi, app, 0);
                        edgeBroker[poi].submitCloudletList(taskList[poi][app]);
                        loadBalancer[poi].balanceTasks(taskList[poi][app], app);
                        //TODO ds this is mine!
                        System.out.printf("%n#-----> Creating %d Task(s) at PoI %d, for App %d at time %.0f sec.%n",
                                tasksToCreate, 9+poi, app, evt.getTime());
                        pDLB = new PoissonDistribution(requestRatePerCell[i][j][app] / SAMPLING_INTERVAL);
                        tasksToCreateLB = pDLB.sample();
                        taskList[9+poi][app] = (ArrayList<TaskSimple>) createTasks(tasksToCreateLB, 9+poi, app, 0);
                        edgeBroker[9+poi].submitCloudletList(taskList[9+poi][app]);
                        loadBalancer[9+poi].balanceTasks(taskList[9+poi][app], app);
//                        for (TaskSimple task : taskList[poi][app]) {
//                            if (task.getVm().getCloudletScheduler().getClass() == CloudletSchedulerTimeShared.class) {
//                                CloudletSchedulerTimeShared sched = (CloudletSchedulerTimeShared) task.getVm().getCloudletScheduler();
//                                System.out.println("Current Mips Share Size: " + sched.getCurrentMipsShare().size());
//                                System.out.println("VM " + task.getVm().getId() + " Number of PES: " + task.getVm().getNumberOfPes());
//                            }
//                        }
                    } else {
                        System.out.printf("%n#-----> Creating %d Task(s) at PoI %d, for App %d at time %.0f sec.%n", 0,
                                poi, app, evt.getTime());
                    }
                }
            }
        }
    }

    // TODO: remove next interval predicted workload when debugging is finished
    private double[][][] createRequestRate(int[][][] assignedUsers, double[] appRequestRatePerUser,
                                           double[][] predictNextIntervalWorkload) {
        double[][][] requestRatePerCellPerApp = new double[GRID_SIZE][GRID_SIZE][APPS];
        int dataRow, dataCol;

        for (int i = 0; i < GRID_SIZE; i++) {
            for (int j = 0; j < GRID_SIZE; j++) {
                for (int app = 0; app < APPS; app++) {
                    if (assignedUsers[i][j][app] != 0) {
                        int distance = CELL_OFFLOADING_DISTANCE_INDEX[i][j];
//                        System.out.println("Distance: " + distance);
//                        System.out.println("Assigned Users: " + assignedUsers[i][j][app]);
                        dataRow = (assignedUsers[i][j][app] * distance) - 1;
                        if (dataRow > simData.length) dataRow = simData.length - 1;
                        dataCol = 12; // TODO: fixed at column 12. Make it Variable
                        requestRatePerCellPerApp[i][j][app] =
                                Math.round((simData[dataRow][dataCol] * appRequestRatePerUser[app]) * 100.0) / 100.0;
                    } else {
                        requestRatePerCellPerApp[i][j][app] = 0;
                    }
                }
            }
        }
        System.out.println("Assigned Users: " + Arrays.deepToString(assignedUsers));
        System.out.println("Request Rate to generate: " + Arrays.deepToString(requestRatePerCellPerApp));
        System.out.println("Request Rate predicted: " + Arrays.deepToString(predictNextIntervalWorkload));

        return requestRatePerCellPerApp;
    }

    private int[][][] createUsers(int gridSize, Group[] groups) {
        Random random = new Random();
        int[][][] usersPerCell = new int[gridSize][gridSize][APPS];

        for (Group group : groups) {
//            System.out.println("Group Size: " + group.size);
            usersPerCell[group.currPos.x][group.currPos.y][group.app] += group.size - 1 + random.nextInt(2);
//            System.out.println("Users in this cel: " + usersPerCell[group.currPos.x][group.currPos.y]);
        }

        for (int i = 0; i < GRID_SIZE; i++) {
            for (int j = 0; j < GRID_SIZE; j++) {
                for (int app = 0; app < APPS; app++) {
                    if (usersPerCell[i][j][app] < 0) usersPerCell[i][j][app] = 0;
                }
            }
        }

//        System.out.println("Users Per Cell");
//        for (int[][] line : usersPerCell) {
//            for (int[] tile : line) {
//                System.out.print(Arrays.toString(tile) + " ");
//            }
//            System.out.println();
//        }
//        System.out.println("-----------");

        return usersPerCell;
    }

    private Datacenter createDatacenter(int hosts, int hostPes, int hostPeMips, int hostRam, int hostBw) {
        final List<Host> hostList = new ArrayList<>(hosts);
        for(int i = 0; i < hosts; i++) {
            Host host = createHost(hostPes, hostPeMips, hostRam, hostBw);
            hostList.add(host);
        }

        //Uses a VmAllocationPolicySimple by default to allocate VMs
        final Datacenter dc = new DatacenterSimple(simulation, hostList, new VmAllocationPolicySimple());
        dc.setSchedulingInterval(SCHEDULING_INTERVAL);
        return dc;
    }

    private Host createHost(int hostPes, int hostPeMips, int hostRam, int hostBw) {
        final List<Pe> peList = new ArrayList<>(hostPes);
        // List of Host's CPUs (Processing Elements, PEs)
        for (int i = 0; i < hostPes; i++) {
            // Uses a PeProvisionerSimple by default to provision PEs for VMs
            peList.add(new PeSimple(hostPeMips));
        }

        final long ram = hostRam; //in Megabytes
        final long bw = hostBw; //in Megabits/s
        final long storage = 1000000; //in Megabytes

        ResourceProvisioner ramProvisioner = new ResourceProvisionerSimple();
        ResourceProvisioner bwProvisioner = new ResourceProvisionerSimple();
        VmScheduler vmScheduler = new VmSchedulerTimeShared();
        Host host = new HostSimple(ram, bw, storage, peList);
        host
            .setRamProvisioner(ramProvisioner)
            .setBwProvisioner(bwProvisioner)
            .setVmScheduler(vmScheduler);
        return host;
    }

    private ArrayList<Vm> createVms(int noOfVms, int poi, int app, int flavor, int host, int vmId) {
        int vm_pes = VM_PES[app][flavor];
        int vm_pe_mips = VM_PE_MIPS[app][flavor];
        int vm_ram = VM_RAM;
        int vm_bw = VM_BW;
        final ArrayList<Vm> list = new ArrayList<>(noOfVms);
        for (int i = 0; i < noOfVms; i++) {
//            System.out.printf("... Spawning %d VM(s) with the following specs: \n", noOfVms);
//            System.out.println(" - VM Flavor: " + flavor);
//            System.out.println(" - VM Cores: " + vm_pes);
            //Uses a CloudletSchedulerTimeShared by default to schedule Cloudlets
            CloudletSchedulerTimeSharedExtended cloudletScheduler = new CloudletSchedulerTimeSharedExtended();
            final Vm vm = new VmSimple(vm_pe_mips, vm_pes);
            vm.setId(poi * 1000 + host * 100 + app * 10 + vmId);
            vm.setRam(vm_ram).setBw(vm_bw).setSize(1000);
            vm.setCloudletScheduler(cloudletScheduler); // TODO: not sure if suppressing is better or real issue exists
            list.add(vm);
        }
        return list;
    }

    private List<TaskSimple> createTasks(int noOfTasks, int poi, int app, int interArrivalTime) {
        final List<TaskSimple> tempTaskList = new ArrayList<>(noOfTasks);

        //UtilizationModel defining the Tasks use up to 90% of any resource all the time
        final UtilizationModelDynamic utilizationModel = new UtilizationModelDynamic(0.9);

        int submissionDelay = 0;
        for (int i = 0; i < noOfTasks; i++) {
            final TaskSimple task = new TaskSimple(TASK_LENGTH, TASK_PES, utilizationModel);
            task.setUtilizationModelRam(UtilizationModel.NULL); // TODO: reconsider if we care about RAM and BW Utilization
            task.setUtilizationModelBw(UtilizationModel.NULL);
            task.setId(Long.parseLong((poi * 10 + app) + Integer.toString(taskCounter[poi][app])));
            task.setSizes(1024);
            task.setSubmissionDelay(submissionDelay);
            task.setBroker(edgeBroker[poi]);
            tempTaskList.add(task);
            submissionDelay += interArrivalTime;
            taskCounter[poi][app]++;
        }

        return tempTaskList;
    }

    private void createGroups(int howManyGroups, int groupSize, int apps, int gridSize) {
        groups = new Group[howManyGroups];
        for (int group = 0; group < howManyGroups; group++) {
            Random rand = new Random();
            int size = 1 + rand.nextInt(groupSize);
            int app = rand.nextInt(apps);
            Coordinates currPos = new Coordinates(rand.nextInt(gridSize), rand.nextInt(gridSize));
            groups[group] = new Group(group, size, app, currPos, gridSize, NMMC_HISTORY);
        }
    }

    private void createBrokersAndDatacenters(int pois) {
        edgeBroker = new DatacenterBrokerSimpleExtended[pois];
        for (int poi = 0; poi < pois; poi++) {
            Set<Datacenter> edgeDCList = new HashSet<>();
            Datacenter dc = createDatacenter(EDGE_HOSTS, EDGE_HOST_PES, EDGE_HOST_PE_MIPS, EDGE_HOST_RAM, EDGE_HOST_BW);
            dc.setName("DataCenter" + poi);
            edgeDCList.add(dc);
            edgeBroker[poi] = new DatacenterBrokerSimpleExtended(simulation);
            edgeBroker[poi].setName("AccessPoint" + poi);
            edgeBroker[poi].setDatacenterList(edgeDCList);
        }
    }

    private void createLoadBalancers(ArrayList<Vm>[] vmPool) {
        loadBalancer = new LoadBalancer[2*POI];
        for (int poi = 0; poi < 2*POI; poi++) {
            loadBalancer[poi] = new LoadBalancer(vmPool[poi], APPS, poi);}
    }

    private void destroyVms() {
        System.out.println("\n--------- DESTROYING VMS ---------\n");
        for (int poi = 0; poi < POI; poi++) {
//            System.out.println("POI: " + poi);
            for (int hostID = 0; hostID < EDGE_HOSTS; hostID++) {
                Host host = edgeBroker[poi].getDatacenterList().get(0).getHost(hostID);
                for (Vm vm: host.getVmCreatedList()){
                    vm.setFailed(true);
                    vm.getHost().getVmScheduler().deallocatePesFromVm(vm);
                    host.destroyVm(vm);
                }
            }
        }
    }

    private ArrayList<Vm>[] spawnVms(ArrayList<int[][]> feasibleFormations, ArrayList<Integer>[] vmPlacement) {
        ArrayList<Vm>[] vmPool = new ArrayList[2*POI];

        // Destroy existing VMs
        destroyVms();

//        System.out.println("Feasible Formations: ");
//        int formation = 0;
//        for (int[][] ff : feasibleFormations) {
//            System.out.println(formation + " -> " + Arrays.deepToString(ff));
//            formation++;
//        }

        // Spawn new VMs as instructed
        System.out.println("\n--------- SPAWNING VMS ---------\n");
        for (int poi = 0; poi < POI; poi++) {
            vmPool[poi] = new ArrayList<>();
            ArrayList<Vm> tempVmList = new ArrayList();
//            System.out.println("POI: " + poi);
            for (int host = 0; host < vmPlacement[poi].size(); host++) {
//                System.out.println(" Host: " + host);
                for (int app = 0; app < APPS; app++) {
//                    System.out.println("  App: " + app);
                    for (int vm = 0; vm < feasibleFormations.get(vmPlacement[poi].get(host))[app].length; vm++) {
                        int vmCores = feasibleFormations.get(vmPlacement[poi].get(host))[app][vm];
                        int vmFlavor = ArrayUtils.indexOf(VM_PES[app], vmCores);
//                        System.out.println("Host Type Vm Types for this app: " + Arrays.toString(feasibleFormations.get(vmPlacement[poi].get(host))[app]));
                        vmList[poi][app] = createVms(1, poi, app, vmFlavor, host, vm);
                        tempVmList.addAll(vmList[poi][app]);
                        vmPool[poi].addAll(vmList[poi][app]);
                        if (vmList[poi][app].size() > maxVmSize) maxVmSize = vmList[poi][app].size();
                    }
                }
            }
            edgeBroker[poi].submitVmList(tempVmList);
            correctlySetVmDescriptions(tempVmList);
        }

        // Debug Vm pool
//        for (int poi = 0; poi < POI; poi++) {
//            System.out.println("--- VM POOL at POI: " + poi + " ---");
//            for (Vm vm : vmPool[poi])
//                System.out.println("VM ID: " + vm.getId() + ", VM APP: " + vm.getDescription());
//        }
        for (int poi = 9; poi < 2*POI; poi++) {
            vmPool[poi] = new ArrayList<>();
            System.out.println("VM pool per poi 1 " + vmPool[poi]+staticVmList[poi]);
            vmPool[poi].addAll(staticVmList[poi]);
            System.out.println("VM pool per poi" + vmPool[poi]);
        }

        return vmPool;
    }

    private void runSimulationAndPrintResults() {
        simulation.terminateAt(TIME_TO_TERMINATE_SIMULATION);
        simulation.addOnClockTickListener(this::masterOfPuppets);
        simulation.start();
        List<TaskSimple> tasks = new ArrayList<>();
        for (int poi = 0; poi < 2*POI; poi++) {
            tasks.addAll(edgeBroker[poi].getCloudletFinishedList());
        }
        if (!CREATE_NMMC_TRANSITION_MATRIX) new CloudletsTableBuilder(tasks).build();
    }


    private void CalculationofAverageResponseTime(double li, double mi, int ni, int indexofhost) {
        int j = (int) (100*li);
        if (j < 0 || mi <= 0 || ni <= 0)
            throw new IllegalArgumentException("The parameters cannot be negative!");
        if (li==0) {
            AverageResponseTimeTi[indexofhost][(int)j] =0;
        }
        else
        if (li<ni*mi-0.25) {
            ErlangC d=new ErlangC(li,mi,ni);
            double waitProb = d.getProbDelay(li,mi,ni);
            double waitTime = d.getAverageWaitTime(li,mi,ni);
            AverageResponseTimeTi[indexofhost][(int) j] = waitTime;
            //System.out.println(waitProb);
            //System.out.println(waitTime);
        }
        else {
            li = ni*mi-0.25;
            ErlangC d = new ErlangC(li, mi, ni);
            double waitTime = d.getAverageWaitTime(li, mi, ni);
            AverageResponseTimeTi[indexofhost][(int) j] = waitTime;
        }

    }


    public double [] Algorithm1(double [] ServiceRate, double [] NumberofServers,double [][] PredictedWorkload,int app) {
        //TODO ds arrival rate = mi*ni - 0.25 at each time
        double[] ArrivalRate = new double [POI];
        if (app ==0){
            for (int i = 0; i < POI; i++) {
                ArrivalRate[i] = PredictedWorkload[i][0];
            }
        }
        else {
            for (int i = 0; i < POI; i++) {
                ArrivalRate[i] = PredictedWorkload[i][1];
            }
        }
//        for(int i = 0; i < POI; i++) {
//            System.out.println(ArrivalRate[i]);
//        }
//        try
//        {
//            System.in.read();
//        }
//        catch(Exception e)
//        {}

        long thisTime = System.currentTimeMillis();
        double D = 1000000000;
        double Tmax = -2;
        double Tmin = 100;
        double [] Tbefore= new double [POI];
        for (int i = 0; i < POI; i++) {
            lj[i]=0;
            li[i]=0;
            int arrivalrate = (int) (100 * ArrivalRate[i]);
            //System.out.println("arrival rate ");
            Ti[i] = AverageResponseTimeTi[i][arrivalrate];
            Tbefore[i]=Ti[i];
            if (Tmax < Ti[i]) Tmax = Ti[i];
            if (Tmin > Ti[i]) Tmin = Ti[i];
            //System.out.println("Ti "+ Ti[i] + " Host: "+ i + " ArrivalRate: " + ArrivalRate[i] + " Tmax: " + Tmax + " Tmin " + Tmin);
        }
        int counterbreak=0;
        while ((D > d) || (D < -d) ) {
            //System.out.println("arrival rate ");
            int pointerOver = 0;
            int pointerUnder = 0;
            Dtotal = (Tmax + Tmin) / 2;
            //        Log.printFormatted("\t Dtotal : %f     \n",               Dtotal            );
            for (int i = 0; i < POI; i++) {
                fi[i] = 0;
                fj[i] = 0;
                if (AverageResponseTimeTi[i][(int) (100 * ArrivalRate[i])] > Dtotal) {
                    OverloadedCloudlets[pointerOver] = i;
                    pointerOver++;
                } else {
                    UnderloadedCloudlets[pointerUnder] = i;
                    pointerUnder++;
                }
            }
            //System.out.println("PointOver: "+ pointerOver + " PointUnder" + pointerUnder);
            double art = 0;
            double sumfi = 0;
            double sumfj = 0;
            for (int i = 0; i < pointerOver; i++) {
                int temp2 = OverloadedCloudlets[i];
                for (int j = ((int) (100 * ArrivalRate[temp2])); j >100 ; j--) {
                    art = AverageResponseTimeTi[temp2][j];
                    if ((art <= Dtotal * (1 + e)) && (art >= Dtotal * (1 - e))) {
                        fi[i] = +ArrivalRate[temp2] - (double) j / 100;
                    }
                    if (((double) j / 100) > (ServiceRate[temp2] * NumberofServers[temp2] - 0.25))
                        j = 000;

                }
                int j=(int)( ArrivalRate[temp2]*100);
                sumfi = sumfi + fi[i];
            }

            for (int i = 0; i < pointerUnder; i++) {

                int temp1 = UnderloadedCloudlets[i];
                for (int j = (int) (100 * ArrivalRate[temp1]); j < 32000; j++) {
                    art = AverageResponseTimeTi[temp1][j];
                    if ((art <= Dtotal * (1 + e)) && (art>=Dtotal*(1-e))){
                        //if ((art<=Dtotal+e)&&(art>=Dtotal-e)){
                        fj[i] = -ArrivalRate[temp1] + (double) j / 100;
                    }
                    if (((double) j / 100) > (ServiceRate[temp1] * NumberofServers[temp1] - 0.25))
                        j = 32000;
                }
                sumfj = sumfj + fj[i];
            }
            D = sumfi - sumfj;
            if (D > 0) Tmin = Dtotal;
            if (D < 0) Tmax = Dtotal;
            //       Log.printFormatted("\t D : %f  Dtotal %f  Tmin %f Tmax %f  \n",D, Dtotal, Tmin, Tmax);
            //System.out.println("D: " + Dtotal + " Tmin:  " + Tmin + " Tmax:  " + Tmax);
            if (Math.abs(Tmin-Tmax)<0.0000001) counterbreak++;
            if (counterbreak>10) {
                //System.out.println("\t BREAK ! counterbreak: %d   \n\n" +counterbreak);
                break;
            }
        }

        // find overloaded and underloaded cloudlets
        int pointerOver = 0;
        int pointerUnder = 0;
        counterbreak=0;
        int notadjust =0;
        for (int i = 0; i < POI; i++) {
            if (Ti[i] > Dtotal) {
                OverloadedCloudlets[pointerOver] = i;
                pointerOver++;
            } else {
                UnderloadedCloudlets[pointerUnder] = i;
                pointerUnder++;
            }
        }

        // +2 for s,t nodes. 0 to all nodes!!
        double[][] graph = new double[POI + 2][POI + 2];
        for (int i = 0; i < POI + 2; i++)  // Vs = OverloadedCloudlets.get[i];
            for (int j = 0; j < POI + 2; j++)
                graph[i][j] = 0;

        double Daverage = 100000000;
        while (((Dtotal - Daverage) > u) || (Dtotal - Daverage < -u)) {
            //         Log.printFormatted("\t PointOver %d  PointUnder %d\n",pointerOver, pointerUnder);
            for (int i = 0; i < POI ; i++) {
                lj[i] = 0;
                li[i] = 0;
            }

            double art = 0;
            for (int i = 0; i < pointerOver; i++) { // Vs = OverloadedCloudlets.get[i];
                int temp2 = OverloadedCloudlets[i];
                //    for (int j = 100; j < (int) (100 * ArrivalRate[temp2]); j++) {
                for (int j = (int) (100 * ArrivalRate[temp2]); j > 100 ; j--) {
                    art = AverageResponseTimeTi[temp2][j];
                    if ((art <= Dtotal * (1 + e)) && (art >= Dtotal * (1 - e))) {
                        //if ((art<=Dtotal+e)&&(art>=Dtotal-e)){
                        fi[i] = +ArrivalRate[temp2] - (double) j / 100;
                        //        Log.printFormatted("\t Host %d art : %f     Flow Over: %f   \n",temp2, art, fi[i]);
                    }
                    if (((double) j / 100) > (ServiceRate[temp2] * NumberofServers[temp2] - 0.25)) j = 0;
                    if (fi[i] < 0) fi[i] = 0;
                }
                graph[0][1+ i] = fi[i];
            }

            for (int i = 0; i < pointerUnder; i++) {
                int temp1 = UnderloadedCloudlets[i];
                for (int j = (int) (100 * ArrivalRate[temp1]); j < 32000; j++) {
                    art = AverageResponseTimeTi[temp1][j];
                    if ((art <= Dtotal * (1 + e)) && (art>=Dtotal*(1-e))){
                        //if ((art<=Dtotal+e)&&(art>=Dtotal-e)){
                        fj[i] = -ArrivalRate[temp1] + (double) j / 100;
                        //               Log.printFormatted("\t Host %d art : %f     Flow Under: %f \n",temp1, art, fj[i]);
                    }
                    if (((double) j / 100 )> (ServiceRate[temp1] * NumberofServers[temp1] - 0.25))
                        j = 32000;
                    if (fj[i] < 0) fj[i] = 0;
                }
                graph[POI - pointerUnder + 1 + i][POI + 1] = fj[i];
            }

            for (int i = 0; i < pointerOver; i++) { // Vs = OverloadedCloudlets.get[i];
                for (int j = 0; j < pointerUnder; j++) {
                    int temp1 = UnderloadedCloudlets[j];
                    int temp2 = OverloadedCloudlets[i];
                    graph[1 + i][POI - pointerUnder + 1 + j] = Math.min(graph[0][1 + i], graph[POI - pointerUnder + 1 + j][POI + 1]);
                }
            }
            // MIN MAX FLOW WITH (Dtotal,Vs,Vt,e)
            double[][] skata = new double[POI + 2][POI + 2];
            skata = MinCostMaxFlow.main(graph,NetDelay,POI+2);
            //skata = FordFulkerson.main(graph, POI + 2);
            double[] Dj = new double[POI];
            double maxDj = -20000;
            for (int i = 0; i < pointerUnder; i++) {
                int temp1 = UnderloadedCloudlets[i];
                lj[i] = ArrivalRate[temp1];
                double sumFi = 0;
                double Tnet = 0;
                for (int k = 0; k < pointerOver; k++) {    // k=1=s korifi mexri pointover dhladi ola ta overloaded gia to sugkekrimeno i = underloaded
                    sumFi = sumFi + skata[POI - pointerUnder +1+ i][k+1];  // eiserxomeni roh
                    li[k]=li[k] + skata[POI - pointerUnder +1+ i][k+1] ;
                    Tnet = Tnet + Math.max(0, skata[k+1][POI - pointerUnder + 1 + i]) * NetDelay[temp1][k];
                }
                lj[i] = lj[i] + sumFi;
                //         Log.printFormatted("\t li: %f  lj : %f  sumFi: %f ArrivalRate: %f      \n",li[0], lj[i], sumFi, ArrivalRate[temp1]);
                Dj[i] = AverageResponseTimeTi[temp1][(int) (lj[i]*100)] + Tnet;  //htan 10
                if (Dj[i] > maxDj) maxDj = Dj[i];
            }
            Daverage = maxDj;
            Dtotal = (Dtotal + Daverage) / 2;
            counterbreak++;
            if (counterbreak>20) {
                System.out.println("\t BREAK2 ! counterbreak:" + counterbreak);
                notadjust=1;
                break;
            }
        }
        System.out.println(pointerOver);
        System.out.println(pointerUnder);
        // overloaded cloudlets apo host 0 mexri pointover
        // underloaded cloudlets apo host overloaded+1 mexri HOSTS
        if (notadjust==0) {
            for (int i = 0; i < pointerOver; i++) {
                int temp2 = OverloadedCloudlets[i];
                System.out.println("\t Host :" +temp2 + "  PREVIOUS ArrivalRate: " + ArrivalRate[temp2]);
                ArrivalRate[temp2] = ArrivalRate[temp2] - li[i];
                if (ArrivalRate[temp2] < 0.1) ArrivalRate[temp2] = 0.1;
                System.out.println("\t Host :" +temp2 + "  Next ArrivalRate: " + ArrivalRate[temp2]);
            }
            for (int i = 0; i < pointerUnder; i++) {
                int temp1 = UnderloadedCloudlets[i];
                System.out.println("\t Host :" +temp1 + "  PREVIOUS ArrivalRate: " + ArrivalRate[temp1]);
                ArrivalRate[temp1] = lj[i];
                if (ArrivalRate[temp1] < 0.1) ArrivalRate[temp1] = 0.1;
                System.out.println("\t Host :" +temp1 + "  Next ArrivalRate: " + ArrivalRate[temp1]);
            }
        }

        long endTimee   = System.currentTimeMillis();
        long totalTimee = endTimee - thisTime;
        System.out.println("Time for Algorithm in milliseconds: "+ totalTimee+ " for app: " +app);   // in milliseconds

        return ArrivalRate;
    }

    private ArrayList<Vm>[] spawnStaticVms(ArrayList<int[][]> feasibleFormations, ArrayList<Integer>[] vmPlacement) {
        ArrayList<Vm>[] vmPool = new ArrayList[2*POI];
        // Spawn new VMs as instructed
        System.out.println("\n--------- SPAWNING VMS ---------\n");
        for (int poi = 0; poi < POI; poi++) {
            vmPool[9+poi] = new ArrayList<>();
            ArrayList<Vm> tempVmList = new ArrayList();
//            System.out.println("POI: " + poi);
            for (int host = 0; host < vmPlacement[poi].size(); host++) {
//                System.out.println(" Host: " + host);
                for (int app = 0; app < APPS; app++) {
//                    System.out.println("  App: " + app);
                    for (int vm = 0; vm < feasibleFormations.get(vmPlacement[poi].get(host))[app].length; vm++) {
                        int vmCores = feasibleFormations.get(vmPlacement[poi].get(host))[app][vm];
                        int vmFlavor = ArrayUtils.indexOf(VM_PES[app], vmCores);
//                        System.out.println("Host Type Vm Types for this app: " + Arrays.toString(feasibleFormations.get(vmPlacement[poi].get(host))[app]));
                        vmList[9+poi][app] = createVms(1, poi+9, app, vmFlavor, host, vm);
                        tempVmList.addAll(vmList[9+poi][app]);
                        vmPool[9+poi].addAll(vmList[9+poi][app]);
                        if (vmList[9+poi][app].size() > maxVmSize) maxVmSize = vmList[9+poi][app].size();
                    }
                }
            }
            edgeBroker[9+poi].submitVmList(tempVmList);
            correctlySetVmDescriptions(tempVmList);
        }


        return vmPool;
    }


}
