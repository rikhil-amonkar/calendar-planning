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
    
    BIG = 10**18
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
            if dist[i][k] == BIG:
                continue
            for j in range(n):
                if dist[k][j] != BIG and dist[i][k] + dist[k][j] < dist[i][j]:
                    dist[i][j] = dist[i][k] + dist[k][j]
    
    if n_pass == 0:
        total_time = dist[start_node][end_node]
        if total_time >= BIG:
            print("No valid plan found")
        else:
            print(total_time)
        return
    
    current_time = 0
    cumulative_times = []
    prev_node = start_node
    for node in pass_nodes:
        d = dist[prev_node][node]
        if d >= BIG:
            print("No valid plan found")
            return
        current_time += d
        cumulative_times.append(current_time)
        prev_node = node
    
    d_final = dist[pass_nodes[-1]][end_node]
    if d_final >= BIG:
        print("No valid plan found")
        return
    total_time = current_time + d_final
    print(total_time)
    for t in cumulative_times:
        print(t)

if __name__ == "__main__":
    main()