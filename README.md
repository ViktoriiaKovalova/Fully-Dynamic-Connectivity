# Full-Dynamic-Connectivity
Class DynamicGraph support queries in dynamic graph,
which means that you can add, delete edges and answer queries,
such as 'are two vertices connected?', 'how many components are
in the graph right now?' in O(log n) time.

The interface is now as follows:

    explicit DynamicGraph(int num); // constructing graph with num edges

    int GetComponentsNumber() const; // answering how many components there are

    void AddEdge(int first, int second); // adding the edge to the graph

    void RemoveEdge(int first, int second); // removing the edge
