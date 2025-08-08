import sys

def main():
    data = sys.stdin.read().split()
    if not data:
        return
    
    n = int(data[0])
    m = int(data[1])
    start_node = int(data[2])
    end_node = int(data[3])
    n_pass = int(data[4])
    index = 5
    passes = []
    for i in range(n_pass):
        node = int(data[index])
        seq = int(data[index+1])
        index += 2
        passes.append((node, seq))
    
    passes.sort(key=lambda x: x[1])
    pass_nodes = [node for node, seq in passes]
    
    BIG = 10**9
    graph = [[BIG] * n for _ in range(n)]
    for i in range(n):
        graph[i][i] = 0
        
    for i in range(m):
        u = int(data[index])
        v = int(data[index+1])
        t = int(data[index+2])
        index += 3
        if t < graph[u][v]:
            graph[u][v] = t
    
    dist = [row[:] for row in graph]
    for k in range(n):
        for i in range(n):
            for j in range(n):
                if dist[i][k] < BIG and dist[k][j] < BIG:
                    new_dist = dist[i][k] + dist[k][j]
                    if new_dist < dist[i][j]:
                        dist[i][j] = new_dist
    
    current = start_node
    total_time = 0
    pass_times = []
    
    for node in pass_nodes:
        if dist[current][node] >= BIG:
            print("No valid plan found")
            return
        if current != node:
            total_time += dist[current][node]
            current = node
        pass_times.append(total_time)
    
    if dist[current][end_node] >= BIG:
        print("No valid plan found")
        return
    if current != end_node:
        total_time += dist[current][end_node]
    
    print(total_time)
    for t in pass_times:
        print(t)

if __name__ == "__main__":
    main()