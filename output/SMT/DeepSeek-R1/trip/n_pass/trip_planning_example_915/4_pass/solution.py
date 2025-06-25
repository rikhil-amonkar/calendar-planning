import string
import sys
import bisect

def main():
    data = sys.stdin.read().splitlines()
    if not data:
        print("No solution found")
        return
    
    n = int(data[0])
    constraints = []
    for i in range(1, 1 + n):
        constraints.append(data[i])
    
    graph = {letter: set() for letter in string.ascii_uppercase}
    in_degree = {letter: 0 for letter in string.ascii_uppercase}
    
    for con in constraints:
        words = con.split()
        if not words:
            continue
        u = words[0]
        v = words[-1]
        if u in string.ascii_uppercase and v in string.ascii_uppercase and u != v:
            if v not in graph[u]:
                graph[u].add(v)
                in_degree[v] += 1
                
    zero_degree = sorted([city for city in string.ascii_uppercase if in_degree[city] == 0])
    topo_order = []
    while zero_degree:
        city = zero_degree.pop(0)
        topo_order.append(city)
        for neighbor in graph[city]:
            in_degree[neighbor] -= 1
            if in_degree[neighbor] == 0:
                bisect.insort(zero_degree, neighbor)
                
    if len(topo_order) != 26:
        print("No solution found")
    else:
        day_map = {}
        for idx, city in enumerate(topo_order, start=1):
            day_map[city] = idx
        for city in string.ascii_uppercase:
            print(day_map[city])

if __name__ == "__main__":
    main()