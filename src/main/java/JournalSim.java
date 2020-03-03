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
import java.util.stream.IntStream;

public class JournalSim {
    // TODO: read these values from external file
    // TODO: set debugging toggle and different colors
    // TODO: do not use constants in methods; add them to method call

    // Simulation related constants
    private static final double TIME_TO_TERMINATE_SIMULATION = 360;
    private static final double SCHEDULING_INTERVAL = 1;
    private static final int SAMPLING_INTERVAL = 30;

    // n-MMC related constants
    private static final Boolean CREATE_NMMC_TRANSITION_MATRIX = false;
    private static final int NMMC_HISTORY = 2;

    private static final String SIM_CSV_FILE_LOCATION = "/home/dspath/Documents/Dsgit/leivadeas/netmode-cloudsim/leivaDatas.csv";
    private static final String READ_NMMC_CSV_FILE_LOCATION = "/home/dspath/Documents/Dsgit/leivadeas/netmode-cloudsim/transitionMatrix(2history12000intervals).csv";
    private static final String WRITE_NMMC_CSV_FILE_LOCATION = "/home/dspath/Documents/Dsgit/leivadeas/netmode-cloudsim/transitionMatrix.csv";
    private static final String WRITE_INTERVALS_CSV_FILE_LOCATION = "/home/dspath/Documents/Dsgit/leivadeas/netmode-cloudsim/intervalStats.csv";


    // Environment related constants
    private static final int POI = 9; //define points of interest
    private static final int APPS = 2;
    private static final int GROUPS = 9;
    private static final int NO_OF_DISTANCES = 1;
    private static final int MAX_USERS_PER_CELL = 2;
    private static final int GROUP_SIZE = 8; // [1..10]
    private static final int GRID_SIZE = 3;

    // Edge Servers related constants
    private static final int EDGE_HOSTS = 1;
    private static final int EDGE_HOST_PES = 16;
    private static final int EDGE_HOST_PE_MIPS = 2000;
    private static final int EDGE_HOST_RAM = 64768;
    private static final int EDGE_HOST_BW = 1000000;

    // VM related constants
    private static final int[][] VM_PES = {{1, 2, 4}, {1, 2, 4}, {1, 2, 4}}; // [app][flavor]
    private static final int[][] VM_PE_MIPS = {{2000, 2000, 2000}, {2000, 2000, 2000}, {2000, 2000, 2000}};
    private static final double[][] VM_GUARANTEED_AVG_RR = {{37.35, 82.24, 172.68}, {37.35, 82.24, 172.68}, {37.35, 82.24, 172.68}};
    private static final double[][] VM_GUARANTEED_MAX_RR = {{50.00, 110.00, 210.00}, {50.00, 110.00, 210.00}, {50.00, 110.00, 210.00}};
    private static final int VM_RAM = 4096;
    private static final int VM_BW = 200000;

    // Task related constants
    private static final int TASK_PES = 1;
    private static final int TASK_LENGTH = 1000;

    // Various "global" variables
    private Double[][] simData;
    private int lastAccessed;
    private int maxVmSize;
    private final CloudSim simulation = new CloudSim();
    private DatacenterBrokerSimpleExtended[] edgeBroker;
    private ArrayList<Vm>[][] vmList;
    private ArrayList<TaskSimple>[][] taskList;
    private double [][][] accumulatedCpuUtil;
    private int [][] taskCounter;
    private int lastIntervalFinishTime;
    private HashMap<String, int[]> transitionsLog;
    private HashMap<String, double[]> transitionProbabilitiesMap;
    private String historicState;
    private double[][] requestRatePerCell;
    private Boolean firstEvent;
    private CSVmachine csvm;
    private Group[] groups;

    //TODO ds initilizations
    //Algorithm settings
    private double D=1000000000;
    private double d= 0.11;                            // parameter for |D|<d
    private double e= 0.1;                            // e parameter for accuracy parameter
    private double u= 0.1;                             // theta parameter for accuracy
    //default structure of cloudsimplus
    private double [] Ti = new double [POI];
    private int[] OverloadedCloudlets = new int[POI];
    private int[] UnderloadedCloudlets = new int[POI];
    private double [] fi = new double [POI];
    private double [] fj = new double [POI];
    private double[] lj = new double[POI];  // synolikh roh poy mpenei se kathe underloaded
    private double[] li = new double[POI];
    //private double[] ArrivalRate = new double[POI];
    private double Dtotal;
    private double[][] AverageResponseTimeTi = new double[POI][4000]; // HTAN 80
    private static double[][] NetDelay ={{0.000000,0.174351,0.151792,0.102222,0.121226,0.167159,0.136996,0.151449,0.137782},
            {0.174351,0.000000,0.104213,0.118699,0.187412,0.197028,0.168254,0.144612,0.177855},
            {0.151792,0.104213,0.000000,0.182387,0.133270,0.132010,0.192918,0.146808,0.122887},
            {0.102222,0.118699,0.182387,0.000000,0.189572,0.102149,0.114024,0.154943,0.114506},
            {0.121226,0.187412,0.133270,0.189572,0.000000,0.136235,0.108649,0.182796,0.126507},
            {0.167159,0.197028,0.132010,0.102149,0.136235,0.000000,0.167916,0.115575,0.131254},
            {0.136996,0.168254,0.192918,0.114024,0.108649,0.167916,0.000000,0.191353,0.105500},
            {0.151449,0.144612,0.146808,0.154943,0.182796,0.115575,0.191353,0.000000,0.174703},
            {0.137782,0.177855,0.122887,0.114506,0.126507,0.131254,0.105500,0.174703,0.000000}};
    private double[] ArrivalRate = {2,4.5,2.6,1.4,2.8,5.2,4.5,7.6,1.4};

    public static void main(String[] args) {
        new JournalSim();
    }

    public JournalSim() {
        csvm = new CSVmachine(POI, APPS, SAMPLING_INTERVAL);

        groups = new Group[GROUPS];
        edgeBroker = new DatacenterBrokerSimpleExtended[POI];
        vmList = (ArrayList<Vm>[][]) new ArrayList[POI][APPS];
        taskList = (ArrayList<TaskSimple>[][]) new ArrayList[POI][APPS];
        taskCounter = new int[POI][APPS];

        simData = csvm.readSimCSVData();
        firstEvent = true;
        historicState = "";

        // Create groups with random starting position
        for (int group = 0; group < GROUPS; group++) {
            Random rand = new Random();
            int size = rand.nextInt(GROUP_SIZE);
            int app = rand.nextInt(APPS);
            Coordinates currPos = new Coordinates(rand.nextInt(GRID_SIZE), rand.nextInt(GRID_SIZE));
            groups[group] = new Group(group, size, app, currPos, GRID_SIZE);
        }

        // Add one broker and one datacenter per Point of Interest
        for (int poi = 0; poi < POI; poi++) {
            Set<Datacenter> edgeDCList = new HashSet<>();
            Datacenter dc = createDatacenter(EDGE_HOSTS, EDGE_HOST_PES, EDGE_HOST_PE_MIPS, EDGE_HOST_RAM, EDGE_HOST_BW);
            dc.setName("DataCenter" + poi);
            edgeDCList.add(dc);
            edgeBroker[poi] = new DatacenterBrokerSimpleExtended(simulation);
            edgeBroker[poi].setName("AccessPoint" + poi);
            edgeBroker[poi].setDatacenterList(edgeDCList);
        }

        // Create number of initial VMs for each app
        int flavor = 2;
        int noOfVms = 1; // per app
        for (int poi = 0; poi < POI; poi++) {
            ArrayList<Vm> tempVmList = new ArrayList();
            for (int app = 0; app < APPS; app++) {
                vmList[poi][app] = createVms(noOfVms, poi, app, flavor);
                tempVmList.addAll(vmList[poi][app]);
                if (vmList[poi][app].size() > maxVmSize) maxVmSize = vmList[poi][app].size();
            }
            edgeBroker[poi].submitVmList(tempVmList);
        }

        // Initialize stat-gathering lists
        accumulatedCpuUtil = new double[POI][APPS][maxVmSize]; // TODO (1): reallocate it in every interval taking the number of VMs
                                                                // TODO (2):  of the Cloudlets into consideration;

        transitionsLog = new HashMap<>();
        // TODO: use transition probabilities map to predict incoming workload
        if (!CREATE_NMMC_TRANSITION_MATRIX) {
            transitionProbabilitiesMap = csvm.readNMMCTransitionMatrixCSV();
//            System.out.println("Transition Probabilities Map: ");
//            transitionProbabilitiesMap.entrySet().forEach(entry -> {
//                System.out.println(entry.getKey() + " -> " + Arrays.toString(entry.getValue()));
//            });
        }


        //TODO ds define number of servers and serviceRate per server according to static placement
        //TODO ds perform static placement of vms and hosts for POI 9 -> 18
        double[] ServiceRate = {4.75,2.49,3.48,5.71,4.05,6.75,3.49,3.48,15.71};
        double[] NumberofServers = {2,4,3,4,5,4,5,4,3};
        for (int i = 0; i < POI; i++) {
            for (int j=0; (j < 4000); j++)                      //htan 80
                CalculationofAverageResponseTime( (double)j/100, ServiceRate[i], (int)NumberofServers[i], i);
        }
        Algorithm1(ServiceRate,NumberofServers);
        //TODO ds calculate offline averageResponseTime
        //TODO ds after the estimation of workload load balance it between cloudlets
        //TODO ds call for each time the algorithm per app! feed the algorithm with the placement for each app and the workload for each app


//        runSimulationAndPrintResults();
        int[][] flavorCores = {{1, 2, 4}, {1, 2, 4}};
        //ArrayList<int[][]> feasibleFormations = calculateFeasibleServerFormations(4, flavorCores);
        //double[][] guaranteedWorkload = calculateServerGuaranteedWorkload(feasibleFormations);
        //double[] energyConsumption = calculateServerPowerConsumption(feasibleFormations, EDGE_HOST_PES);
        //double[][] predictedWorkload = {{50, 100}, {200, 400}, {200, 400}, {200, 400}, {200, 400}, {200, 400}, {200, 400}, {200, 400}, {200, 400}};
        //ArrayList<Integer>[] vmPlacement = optimizeVmPlacement(guaranteedWorkload, energyConsumption, 3, predictedWorkload);
        ArrayList<Integer>[] vmPlacement = new ArrayList[POI];
        vmPlacement[0] = new ArrayList<>() ;
        vmPlacement[1] = new ArrayList<>() ;
        vmPlacement[2] = new ArrayList<>() ;
        vmPlacement[3] = new ArrayList<>() ;
        vmPlacement[4] = new ArrayList<>() ;
        vmPlacement[5] = new ArrayList<>() ;
        vmPlacement[6] = new ArrayList<>() ;
        vmPlacement[7] = new ArrayList<>() ;
        vmPlacement[8] = new ArrayList<>() ;
        vmPlacement[0].add(0);
        vmPlacement[0].add(5);
        vmPlacement[1].add(6);
        vmPlacement[1].add(11);
        vmPlacement[1].add(11);
        vmPlacement[2].add(6);
        vmPlacement[2].add(11);
        vmPlacement[2].add(11);
        vmPlacement[3].add(6);
        vmPlacement[3].add(11);
        vmPlacement[3].add(11);
        vmPlacement[4].add(6);
        vmPlacement[4].add(11);
        vmPlacement[4].add(11);
        vmPlacement[5].add(6);
        vmPlacement[5].add(11);
        vmPlacement[5].add(11);
        vmPlacement[6].add(6);
        vmPlacement[6].add(11);
        vmPlacement[6].add(11);
        vmPlacement[7].add(6);
        vmPlacement[7].add(11);
        vmPlacement[7].add(11);
        vmPlacement[8].add(6);
        vmPlacement[8].add(11);
        vmPlacement[8].add(11);


        //TODO ds vmplacement static apo emena! guaranteed bgainei apo to service rate tou placement kai predicted apo mario
        //double [][] work = calculateResidualWorkload(vmPlacement, guaranteedWorkload, predictedWorkload);
        //System.out.println("skata "+work[0][0]);


        runSimulationAndPrintResults();
//        int[][] flavorCores = {{1, 2, 4}, {1, 2, 4}};
//        ArrayList<int[][]> feasibleFormations = calculateFeasibleServerFormations(4, flavorCores);
//        double[][] guaranteedWorkload = calculateServerGuaranteedWorkload(feasibleFormations);
//        double[] energyConsumption = calculateServerPowerConsumption(feasibleFormations, EDGE_HOST_PES);
//        double[][] predictedWorkload = {{50, 100}, {200, 400}, {200, 400}, {200, 400}, {200, 400}, {200, 400}, {200, 400},
//                {200, 400}, {200, 400}};
//        ArrayList<Integer>[] vmPlacement = optimizeVmPlacement(feasibleFormations, guaranteedWorkload, energyConsumption,
//                3, predictedWorkload, 4, 0.5);
//        calculateResidualWorkload(vmPlacement, guaranteedWorkload, predictedWorkload);
//        calculateResidualResources(vmPlacement, 3);


        System.out.println(getClass().getSimpleName() + " finished!");
        if (CREATE_NMMC_TRANSITION_MATRIX) csvm.createNMMCTransitionMatrixCSV(transitionsLog);
    }

    // Take decisions with a second-wise granularity
    private void masterOfPuppets(final EventInfo evt) {
//        System.out.println((int)evt.getTime());
        int[][] assignedUsers;

        // Initial configurations
        if (firstEvent) {
            correctlyCreateVmDescriptions();
            firstEvent = false;
        }

        if (!(lastAccessed == (int) evt.getTime())) {
            collectVmStats();

            // If a full interval has been completed or first interval, predict group movement, actually move group
            // and generate request rate per cell
            if (((int) evt.getTime() % SAMPLING_INTERVAL == 0) || ((int) evt.getTime() < SAMPLING_INTERVAL)) {
                // Predict group movement and random users arrival


                for (Group group : groups) {
                    // Move group
                    group.updateAlreadyAccessed();
                    group.move();
                    if (CREATE_NMMC_TRANSITION_MATRIX) logTransitions(GRID_SIZE * group.currPos.x + group.currPos.y,
                            GRID_SIZE * group.nextPos.x + group.nextPos.y);
                    group.updatePosition();
                }
                assignedUsers = createRandomUsers(GRID_SIZE, groups);
                requestRatePerCell = createRequestRate(assignedUsers);

                // If a full interval has been completed, gather stats and present them
                if ((int) evt.getTime() % SAMPLING_INTERVAL == 0) {
                    // Collect Stats
                    IntervalStats stats =  collectTaskStats();
                    int[][] intervalFinishedTasks = stats.getIntervalFinishedTasks();
                    int[][] intervalAdmittedTasks = stats.getIntervalAdmittedTasks();
                    double[][] accumulatedResponseTime = stats.getAccumulatedResponseTime();
                    csvm.formatAndPrintIntervalStats(vmList, intervalFinishedTasks,
                            intervalAdmittedTasks, accumulatedResponseTime, accumulatedCpuUtil);
                    accumulatedCpuUtil = new double[POI][APPS][maxVmSize];
                    lastIntervalFinishTime = (int) evt.getTime();
                }
            }

            // Create requests based on generated request rate
            int app = 0; // TODO: create workload for more than one apps
            if (!CREATE_NMMC_TRANSITION_MATRIX) generateRequests(requestRatePerCell, evt, app);
            //TODO ds load balancing before that!
            lastAccessed = (int) evt.getTime();
        }
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

    private ArrayList<Integer>[] optimizeVmPlacement(ArrayList<int[][]> feasibleFormations, double[][] guaranteedWorkload,
                                                     double[] energyConsumption, int hosts, double[][] predictedWorkload,
                                                     int edgeHostPes, double cutOffPoint) {
        ArrayList<Integer>[] vmPlacement = new ArrayList[POI];

        // Solve lp optimization
        for (int poi = 0; poi < POI; poi++) {
//            System.out.println(Arrays.deepToString(guaranteedWorkload));
//            System.out.println(Arrays.toString(energyConsumption));
            try {
                vmPlacement[poi] = Optimizer.optimizeVmPlacement(guaranteedWorkload, energyConsumption, hosts, predictedWorkload[poi]);
            } catch (LpSolveException e) {
                e.printStackTrace();
            }
        }
//        System.out.println("\n\n" + Arrays.deepToString(vmPlacement));

        // Cut out "underutilised" servers. Underutilisation criteria = less than 50% of the cores allocated
        for (ArrayList<Integer> site : vmPlacement) {
            for (int server : site) {
                int serverCoreSum = 0;
                for (int app = 0; app < APPS; app++) serverCoreSum += IntStream.of(feasibleFormations.get(server)[app]).sum();
//                System.out.println(serverCoreSum);

                if ((serverCoreSum / (double) edgeHostPes) <= cutOffPoint) site.remove(server);
            }
        }
        System.out.println("Vm Placement: " + Arrays.deepToString(vmPlacement));

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
                for (int flavor : feasibleFormations.get(permutation)[app]) {
//                    System.out.println(ArrayUtils.indexOf(VM_PES[app], flavor));
                    energyConsumption[permutation] += calculateVmPowerConsumption(serverCores, VM_PES[app][flavor], k, pMax);
//                    System.out.println(energyConsumption[permutation]);
                }
            }
        }

        System.out.println("Server Formations Power Consumption: " + Arrays.toString(energyConsumption));

        return energyConsumption;
    }

    // Use Energy Model defined in paper to predict the power consumed by each VM provisioned in a server with an error below 5%
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
        for (int poi = 0; poi < POI; poi++) {
            for (int app = 0; app < APPS; app++) {
                for (int vm = 0; vm < vmList[poi][app].size(); vm++) {
                    accumulatedCpuUtil[poi][app][vm] += vmList[poi][app].get(vm).getCpuPercentUtilization();
//                    System.out.println("VM ID: " + poi + "" + app + "" + vm);
//                    System.out.println("Current CPU Util: " + vmList[poi][app].get(vm).getCpuPercentUtilization());
//                    System.out.println("Total CPU Util: " + accumulatedCpuUtil[poi][app][vm]);
                }
            }
        }
    }

    private IntervalStats collectTaskStats() {
        int[][] intervalFinishedTasks = new int[POI][APPS];
        int[][] intervalAdmittedTasks = new int[POI][APPS];
        double[][] accumulatedResponseTime  = new double[POI][APPS];

        for (int poi = 0; poi < POI; poi++) {
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

        for (int poi = 0; poi < POI; poi++) {
//               System.out.println(edgeBroker[poi].getCloudletFinishedList().size());
//            System.out.println(edgeBroker[poi].getCloudletSubmittedList().size());
            for (Cloudlet c : edgeBroker[poi].getCloudletSubmittedList()) {
                // Ensure that Task has been completed within the Interval
//                System.out.println(c.getLastDatacenterArrivalTime());
//                System.out.println(lastIntervalFinishTime);
                if (c.getLastDatacenterArrivalTime() > lastIntervalFinishTime) {
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

    private void correctlyCreateVmDescriptions() {
        for (int poi = 0; poi < POI; poi++) {
            for (int app = 0; app < APPS; app++) {
                for (int vmi = 0; vmi < vmList[poi][app].size(); vmi++) {
                    Vm vm = vmList[poi][app].get(vmi);
                    vm.setDescription("{\"App\": " + app + " }"); // Vm Description in Json format
                }
            }
        }
    }

    private void logTransitions(int prevState, int nextState) {
        if (historicState.length() > NMMC_HISTORY) historicState = historicState.substring(1); // remove oldest state
        historicState += Integer.toString(prevState); //concat previous state
        if (!transitionsLog.containsKey(historicState)) {
            transitionsLog.put(historicState, new int[POI]); // create the array
        }
//        System.out.println("Previous State: " + prevState);
//        System.out.println("Historic State: " + historicState);
//        System.out.println("Next State: " + nextState);
        transitionsLog.get(historicState)[nextState]++;
        System.out.println("Transition Log: ");
        transitionsLog.entrySet().forEach(entry -> {
            System.out.println(entry.getKey() + " -> " + Arrays.toString(entry.getValue()));
        });
    }

    private void generateRequests(double[][] requestRatePerCell, EventInfo evt, int app) {
        PoissonDistribution pD;
        int tasksToCreate, poi;

        for (int i = 0; i < GRID_SIZE; i++) {
            for (int j = 0; j < GRID_SIZE; j++) {
                poi = GRID_SIZE * i + j;
                if (requestRatePerCell[i][j] != 0) {
                    pD = new PoissonDistribution(requestRatePerCell[i][j] / SAMPLING_INTERVAL);
                    tasksToCreate = pD.sample();
                    taskList[poi][app] = new ArrayList<>();
                    System.out.printf("%n#-----> Creating %d Task(s) at PoI %d, for App %d at time %.0f sec.%n", tasksToCreate, poi, app, evt.getTime());
                    taskList[poi][app] = (ArrayList<TaskSimple>) createTasks(tasksToCreate, poi, app, 0);
                    edgeBroker[poi].submitCloudletList(taskList[poi][app], vmList[poi][app].get(0)); // TODO make app selection + load balancing
                }
                else {
                    System.out.printf("%n#-----> Creating %d Task(s) at PoI %d, for App %d at time %.0f sec.%n", 0, poi, app, evt.getTime());
                }
            }
        }
    }

    private double[][] createRequestRate(int[][] assignedUsers) {
        double[][] requestRatePerCell = new double[GRID_SIZE][GRID_SIZE];
        Random random = new Random(); // randomize distance from cell
        int distance;

        for (int i = 0; i < GRID_SIZE; i++) {
            for (int j = 0; j < GRID_SIZE; j++) {
                if (assignedUsers[i][j] != 0) {
                    distance = random.nextInt(NO_OF_DISTANCES) + 1;
                    requestRatePerCell[i][j] = simData[(assignedUsers[i][j] * distance) - 1][12];
                }
                else {
                    requestRatePerCell[i][j] = 0;
                }
            }
        }
        System.out.println(Arrays.deepToString(assignedUsers));
        System.out.println(Arrays.deepToString(requestRatePerCell));

        return requestRatePerCell;
    }

    private int[][] createRandomUsers(int gridSize, Group[] groups) {
        Random random = new Random();
        int[][] usersPerCell = new int[gridSize][gridSize];

        for (Group group : groups)
            usersPerCell[group.currPos.x][group.currPos.y] += group.size - 1 + random.nextInt(2);
        for (int i = 0; i < GRID_SIZE; i++) {
            for (int j = 0; j < GRID_SIZE; j++) {
                if (usersPerCell[i][j] < 0) usersPerCell[i][j] = 0;
            }
        }
        System.out.println("Users Per Cell");
        for (int[] line : usersPerCell) {
                for (int tile : line) {
                    System.out.print(tile + " ");
                }
                System.out.println();
            }
            System.out.println("-----------");
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
        //List of Host's CPUs (Processing Elements, PEs)
        for (int i = 0; i < hostPes; i++) {
            //Uses a PeProvisionerSimple by default to provision PEs for VMs
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

    private ArrayList<Vm> createVms(int noOfVms, int exhibit, int app, int flavor) {
        int vm_pes = VM_PES[app][flavor - 1];
        int vm_pe_mips = VM_PE_MIPS[app][flavor - 1];
        int vm_ram = VM_RAM;
        int vm_bw = VM_BW;
        final ArrayList<Vm> list = new ArrayList<>(noOfVms);
        for (int i = 0; i < noOfVms; i++) {
            //Uses a CloudletSchedulerTimeShared by default to schedule Cloudlets
            final Vm vm = new VmSimple(vm_pe_mips, vm_pes);
            vm.setId(exhibit * 10 + app);
            vm.setRam(vm_ram).setBw(vm_bw).setSize(1000);
            // Description contains application id
            vm.setDescription(Integer.toString(app));
            list.add(vm);
        }
        return list;
    }

    private List<TaskSimple> createTasks(int noOfTasks, int exhibit, int app, int interArrivalTime) {
        final List<TaskSimple> tempTaskList = new ArrayList<>(noOfTasks);

        //UtilizationModel defining the Tasks use up to 90% of any resource all the time
        final UtilizationModelDynamic utilizationModel = new UtilizationModelDynamic(0.9);

        int submissionDelay = 0;
        for (int i = 0; i < noOfTasks; i++) {
            final TaskSimple task = new TaskSimple(TASK_LENGTH, TASK_PES, utilizationModel);
            task.setUtilizationModelRam(UtilizationModel.NULL); // TODO: reconsider if we care about RAM and BW Utilization
            task.setUtilizationModelBw(UtilizationModel.NULL);
            task.setId(Long.parseLong((exhibit * 10 + app) + Integer.toString(taskCounter[exhibit][app])));
            task.setSizes(1024);
            task.setSubmissionDelay(submissionDelay);
            task.setBroker(edgeBroker[exhibit]);
            tempTaskList.add(task);
            submissionDelay += interArrivalTime;
            taskCounter[exhibit][app]++;
        }

        return tempTaskList;
    }

    private void runSimulationAndPrintResults() {

        simulation.terminateAt(TIME_TO_TERMINATE_SIMULATION);
        simulation.addOnClockTickListener(this::masterOfPuppets);
        simulation.start();
        List<TaskSimple> tasks = new ArrayList<>();
        for (int poi = 0; poi < POI; poi++) {
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


    public void Algorithm1(double [] ServiceRate, double [] NumberofServers) {
        // TODO should read arrivalrate from predicted workload for each cite!

        long thisTime = System.currentTimeMillis();
        double D = 1000000000;
        double Tmax = -2;
        double Tmin = 100;
        double [] Tbefore= new double [POI];
        for (int i = 0; i < POI; i++) {
            lj[i]=0;
            li[i]=0;
            int arrivalrate = (int) (100 * ArrivalRate[i]);
            Ti[i] = AverageResponseTimeTi[i][arrivalrate];
            Tbefore[i]=Ti[i];
            if (Tmax < Ti[i]) Tmax = Ti[i];
            if (Tmin > Ti[i]) Tmin = Ti[i];
            //System.out.println("Ti "+ Ti[i] + " Host: "+ i + " ArrivalRate: " + ArrivalRate[i] + " Tmax: " + Tmax + " Tmin " + Tmin);
        }
        int counterbreak=0;
        while ((D > d) || (D < -d) ) {
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
                for (int j = (int) (100 * ArrivalRate[temp1]); j < 4000; j++) {
                    art = AverageResponseTimeTi[temp1][j];
                    if ((art <= Dtotal * (1 + e)) && (art>=Dtotal*(1-e))){
                        //if ((art<=Dtotal+e)&&(art>=Dtotal-e)){
                        fj[i] = -ArrivalRate[temp1] + (double) j / 100;
                    }
                    if (((double) j / 100) > (ServiceRate[temp1] * NumberofServers[temp1] - 0.25))
                        j = 4000;
                }
                sumfj = sumfj + fj[i];
            }
            D = sumfi - sumfj;
            if (D > 0) Tmin = Dtotal;
            if (D < 0) Tmax = Dtotal;
            //       Log.printFormatted("\t D : %f  Dtotal %f  Tmin %f Tmax %f  \n",D, Dtotal, Tmin, Tmax);
            //System.out.println("D: " + Dtotal + " Tmin:  " + Tmin + " Tmax:  " + Tmax);
            if (Math.abs(Tmin-Tmax)<0.0000001) counterbreak++;
            //if (counterbreak>10) {
            //    //Log.printFormatted("\t BREAK ! counterbreak: %d   \n\n",counterbreak);
            //    break;
            //}
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
                for (int j = (int) (100 * ArrivalRate[temp1]); j < 4000; j++) {
                    art = AverageResponseTimeTi[temp1][j];
                    if ((art <= Dtotal * (1 + e)) && (art>=Dtotal*(1-e))){
                        //if ((art<=Dtotal+e)&&(art>=Dtotal-e)){
                        fj[i] = -ArrivalRate[temp1] + (double) j / 100;
                        //               Log.printFormatted("\t Host %d art : %f     Flow Under: %f \n",temp1, art, fj[i]);
                    }
                    if (((double) j / 100 )> (ServiceRate[temp1] * NumberofServers[temp1] - 0.25))
                        j = 4000;
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
        System.out.println(totalTimee);   // in milliseconds
        //TODO ds should return arrivalRate per cite
    }

}
