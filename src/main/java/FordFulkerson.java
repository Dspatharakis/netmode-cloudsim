/**
 * Created by Abdul on 10/18/2017. Stolen From geeksforgeeks
 */

import java.util.*;
import java.lang.*;
import java.io.*;
import java.util.LinkedList;

public class FordFulkerson{



    public static double [][] main (double graph [][], int V)//int graph [][], int V)
    {
       //final int V = 6; //Number of vertices in graph
        // Let us create a graph shown in the above example
    /*    double graph[][] =new double[][] {
            {0, 16.412, 13.123, 0, 0, 0},
            {0, 0, 10, 12.224, 0, 0},
            {0, 4.123, 0, 0, 14.123, 0},
            {0, 0, 9, 0, 0, 20},
            {0, 0, 0, 7, 0, 4},
            {0, 0, 0, 0, 0, 0}
        };
*/

        FordFulkerson m = new FordFulkerson();
        return m.fordFulkerson(graph, 0, V-1, V);
/*
        System.out.println("The maximum possible flow is " +
            m.fordFulkerson(graph, 0, 5, V));
  */

    }


    /* Returns true if there is a path from source 's' to sink
      't' in residual graph. Also fills parent[] to store the
      path */
    boolean bfs(double rGraph[][], int s, int t, int parent[],int V)
    {
        // Create a visited array and mark all vertices as not
        // visited
        boolean visited[] = new boolean[V];
        for(int i=0; i<V; ++i)
            visited[i]=false;

        // Create a queue, enqueue source vertex and mark
        // source vertex as visited
        LinkedList<Integer> queue = new LinkedList<Integer>();
        queue.add(s);
        visited[s] = true;
        parent[s]=-1;

        // Standard BFS Loop
        while (queue.size()!=0)
        {
            int u = queue.poll();

            for (int v=0; v<V; v++)
            {
                if (visited[v]==false && rGraph[u][v] > 0)
                {
                    queue.add(v);
                    parent[v] = u;
                    visited[v] = true;
                }
            }
        }

        // If we reached sink in BFS starting from source, then
        // return true, else false
        return (visited[t] == true);
    }

    // Returns tne maximum flow from s to t in the given graph
    double[][] fordFulkerson(double graph[][], int s, int t, int V)
    {
        int u, v;

        // Create a residual graph and fill the residual graph
        // with given capacities in the original graph as
        // residual capacities in residual graph

        // Residual graph where rGraph[i][j] indicates
        // residual capacity of edge from i to j (if there
        // is an edge. If rGraph[i][j] is 0, then there is
        // not)
        double rGraph[][] = new double [V][V];
        double sGraph[][] = new double [V][V];

        for (u = 0; u < V; u++)
            for (v = 0; v < V; v++)
                rGraph[u][v] = graph[u][v];

        // This array is filled by BFS and to store path
        int parent[] = new int[V];

        int max_flow = 0;  // There is no flow initially

        // Augment the flow while tere is path from source
        // to sink
        while (bfs(rGraph, s, t, parent,V))
        {
            // Find minimum residual capacity of the edhes
            // along the path filled by BFS. Or we can say
            // find the maximum flow through the path found.
            double path_flow = Double.MAX_VALUE;
            for (v=t; v!=s; v=parent[v])
            {
                u = parent[v];
                path_flow = Math.min(path_flow, rGraph[u][v]);
            }

            // update residual capacities of the edges and
            // reverse edges along the path
            for (v=t; v != s; v=parent[v])
            {
                u = parent[v];
                rGraph[u][v] -= path_flow;
                rGraph[v][u] += path_flow;
                sGraph[v][u]+= path_flow ;
            }

            // Add path flow to overall flow
            max_flow += path_flow;
        }

        // Return the overall flow
        //return max_flow;
        return sGraph;

    }

    // Driver program to test above functions


}
