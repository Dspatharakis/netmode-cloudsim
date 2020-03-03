/**
 * Created by Abdul on 2/1/2018.
 */
import java.util.*;
import java.lang.*;

public class MinCostMaxFlow {

    static class Edge {
        int to, f, cap, cost, rev;

        Edge(int v, int cap, int cost, int rev) {
            this.to = v;
            this.cap = cap;
            this.cost = cost;
            this.rev = rev;
        }
    }

    public static List<Edge>[] createGraph(int n) {
        List<Edge>[] graph = new List[n];
        for (int i = 0; i < n; i++)
            graph[i] = new ArrayList<Edge>();
        return graph;
    }

    public static void addEdge(List<Edge>[] graph, int s, int t, int cap, int cost) {
        graph[s].add(new Edge(t, cap, cost, graph[t].size()));
        graph[t].add(new Edge(s, 0, -cost, graph[s].size() - 1));
    }

    static void bellmanFord(List<Edge>[] graph, int s, int[] dist, int[] prevnode, int[] prevedge, int[] curflow) {
        int n = graph.length;
        Arrays.fill(dist, 0, n, Integer.MAX_VALUE);
        dist[s] = 0;
        curflow[s] = Integer.MAX_VALUE;
        boolean[] inqueue = new boolean[n];
        int[] q = new int[n];
        int qt = 0;
        q[qt++] = s;
        for (int qh = 0; (qh - qt) % n != 0; qh++) {
            int u = q[qh % n];
            inqueue[u] = false;
            for (int i = 0; i < graph[u].size(); i++) {
                Edge e = graph[u].get(i);
                if (e.f >= e.cap)
                    continue;
                int v = e.to;
                int ndist = dist[u] + e.cost;
                if (dist[v] > ndist) {
                    dist[v] = ndist;
                    prevnode[v] = u;
                    prevedge[v] = i;
                    curflow[v] = Math.min(curflow[u], e.cap - e.f);
                    if (!inqueue[v]) {
                        inqueue[v] = true;
                        q[qt++ % n] = v;
                    }
                }
            }
        }
    }

    public static int[] minCostFlow(List<Edge>[] graph, int s, int t, int maxf,double [][] flows) {
        int n = graph.length;
        int[] dist = new int[n];
        int[] curflow = new int[n];
        int[] prevedge = new int[n];
        int[] prevnode = new int[n];

        int flow = 0;
        int flowCost = 0;
        while (flow < maxf) {
            bellmanFord(graph, s, dist, prevnode, prevedge, curflow);
            if (dist[t] == Integer.MAX_VALUE)
                break;
            int df = Math.min(curflow[t], maxf - flow);
            flow += df;
            for (int v = t; v != s; v = prevnode[v]) {
                Edge e = graph[prevnode[v]].get(prevedge[v]);
                e.f += df;
                graph[v].get(e.rev).f -= df;
                flowCost += df * e.cost;
      //          System.out.format("[%d,%d],%d \n", v,prevnode[v],df);
                flows[prevnode[v]][v]+=df;
            }
        }
        return new int[]{flow, flowCost};
    }

    // Usage example
    public static double [][] main(double graph1 [][],double cost1[][], int V) {
        List<Edge>[] graph = createGraph(V);
        double[][] flows= new double [V][V];
        double cost[][]= new double[V][V];
        for (int i = 0; i < V; i++){
            for (int j = 0; j < V; j++) {
                if (i==0)
                    cost[i][j]=0;
                else if (i==V-1)
                    cost[i][j]=0;
                else if (j==0)
                    cost[i][j]=0;
                else if (j==V-1)
                    cost[i][j]=0;
                else
                    cost[i][j]=cost1[i-1][j-1];
             //   System.out.format("[%d,%d],%d \n", i,j, flows[i][j]);
                addEdge(graph,i,j,(int)(100*graph1[i][j]),(int)(100*cost[i][j]));
            }}

   /*     addEdge(graph, 0, 1, 3, 1);
        addEdge(graph, 0, 2, 4, 2);
        addEdge(graph, 0, 3, 5, 0);
        addEdge(graph, 1, 2, 2, 0);
        addEdge(graph, 2, 3, 4, 0);
        addEdge(graph, 2, 4, 1, 0);
        addEdge(graph, 3, 4, 10, 0);
   */     int[] res = minCostFlow(graph, 0, V-1, Integer.MAX_VALUE,flows);
  //      int flow = res[0];
  //      int flowCost = res[1];
   //     System.out.println( flow);
   //     System.out.println( flowCost);

    /*    for (int i = 0; i < 5; i++){
            for (int j = 0; j < 5; j++) {
                System.out.format("[%d,%d],%d \n", i,j, flows[i][j]);
            }}
*/

        for (int i = 0; i < V; i++){
            for (int j = 0; j < V; j++) {
                flows[j][i]=flows[i][j]/100;
            }}
        return flows;
    }
}

