from collections import deque

def plan_trip(n, lengths, dependencies):
    if n == 0:
        return [], 0
    if n == 1:
        # Only valid if there are no dependencies
        if len(dependencies) > 0:
            return None, None
        return [0], lengths[0]
    
    # Build graph and in_degree arrays
    graph = [[] for _ in range(n)]
    in_degree = [0] * n
    
    # Populate graph and in_degree from dependencies
    for i, j in dependencies:
        graph[i].append(j)
        in_degree[j] += 1
    
    # Verify start/end conditions
    if in_degree[0] != 0 or len(graph[n-1]) != 0:
        return None, None
    
    # Special case for exactly 2 activities
    if n == 2:
        return [0, n-1], sum(lengths)
    
    # Process subgraph (nodes 0 to n-2)
    n_sub = n - 1
    graph_sub = [[] for _ in range(n_sub)]
    in_degree_sub = [0] * n_sub
    
    # Build subgraph excluding n-1
    for i in range(n_sub):
        for j in graph[i]:
            if j == n-1:
                continue
            graph_sub[i].append(j)
            in_degree_sub[j] += 1
    
    # Initialize queue with node 0
    q = deque()
    if in_degree_sub[0] != 0:
        return None, None
    q.append(0)
    
    # Perform topological sort
    order_sub = []
    processed = 0
    
    while q:
        node = q.popleft()
        order_sub.append(node)
        processed += 1
        for neighbor in graph_sub[node]:
            in_degree_sub[neighbor] -= 1
            if in_degree_sub[neighbor] == 0:
                q.append(neighbor)
    
    # Verify all nodes were processed
    if processed != n_sub:
        return None, None
    
    # Final order combines subgraph order and last activity
    order = order_sub + [n-1]
    total_time = sum(lengths)
    return order, total_time

def main():
    import json
    import sys
    
    data = json.load(sys.stdin)
    activities = data["activities"]
    n = len(activities)
    lengths = [act["length"] for act in activities]
    dependencies = data["dependencies"]
    
    # Convert dependencies to tuples
    dep_tuples = []
    for dep in dependencies:
        dep_tuples.append((dep["from"], dep["to"]))
    
    order, total_time = plan_trip(n, lengths, dep_tuples)
    
    if order is None:
        print(json.dumps({"error": "No solution found"}))
    else:
        result = {
            "order": order,
            "total_time": total_time
        }
        print(json.dumps(result))

if __name__ == '__main__':
    main()