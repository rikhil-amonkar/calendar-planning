from collections import deque
import sys
sys.setrecursionlimit(10000)

graph = {
    'Amsterdam': ['Dublin', 'Brussels', 'Helsinki', 'Munich'],
    'Athens': ['Prague', 'Valencia', 'Munich', 'Stockholm', 'Helsinki'],
    'Brussels': ['Amsterdam', 'Dublin', 'Prague', 'Munich'],
    'Dublin': ['Amsterdam', 'Brussels', 'Prague', 'Valencia', 'Porto'],
    'Helsinki': ['Amsterdam', 'Athens', 'Stockholm', 'Reykjavik'],
    'Lyon': ['Valencia', 'Munich', 'Naples', 'Split'],
    'Munich': ['Amsterdam', 'Athens', 'Brussels', 'Dublin', 'Lyon', 'Prague', 'Valencia', 'Warsaw'],
    'Naples': ['Lyon', 'Prague', 'Valencia', 'Warsaw'],
    'Porto': ['Dublin', 'Valencia'],
    'Prague': ['Athens', 'Brussels', 'Dublin', 'Munich', 'Naples', 'Stockholm', 'Warsaw'],
    'Reykjavik': ['Helsinki', 'Warsaw'],
    'Split': ['Lyon', 'Warsaw'],
    'Stockholm': ['Athens', 'Helsinki', 'Prague'],
    'Valencia': ['Athens', 'Dublin', 'Lyon', 'Munich', 'Naples', 'Porto'],
    'Warsaw': ['Munich', 'Naples', 'Prague', 'Split', 'Reykjavik']
}

all_cities = sorted(graph.keys())
n = len(all_cities)
city_to_index = {city: idx for idx, city in enumerate(all_cities)}
full_mask = (1 << n) - 1

memo = {}
def dfs(current, mask):
    if mask == full_mask:
        if current == 'Split':
            return [current]
        else:
            return None
    key = (current, mask)
    if key in memo:
        return memo[key]
    for neighbor in graph[current]:
        idx = city_to_index[neighbor]
        if mask & (1 << idx):
            continue
        new_mask = mask | (1 << idx)
        res = dfs(neighbor, new_mask)
        if res is not None:
            path = [current] + res
            memo[key] = path
            return path
    memo[key] = None
    return None

start_mask = 1 << city_to_index['Porto']
path = dfs('Porto', start_mask)

if path is None:
    print("No Hamiltonian path found")
else:
    skip_indices = [5, 10]
    current_day = 1
    itinerary = []
    itinerary.append(f"Day {current_day}: Stay in {path[0]}")
    current_day += 1

    for i in range(1, len(path)):
        itinerary.append(f"Day {current_day}: Fly from {path[i-1]} to {path[i]}")
        current_day += 1
        if i == len(path) - 1:
            itinerary.append(f"Day {current_day}: Stay in {path[i]}")
        else:
            if i in skip_indices:
                continue
            else:
                itinerary.append(f"Day {current_day}: Stay in {path[i]}")
                current_day += 1

    for line in itinerary:
        print(line)