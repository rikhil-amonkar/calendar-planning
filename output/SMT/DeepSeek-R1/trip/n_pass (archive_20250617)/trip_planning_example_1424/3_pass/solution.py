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

cities_list = sorted(graph.keys())
n = len(cities_list)
city_to_index = {city: idx for idx, city in enumerate(cities_list)}
index_to_city = {idx: city for idx, city in enumerate(cities_list)}

start_city = 'Porto'
end_city = 'Split'
start_index = city_to_index[start_city]
end_index = city_to_index[end_city]

all_done = (1 << n) - 1

memo = {}

def dfs(current, mask):
    if mask == all_done:
        if current == end_city:
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

start_mask = 1 << start_index
path = dfs(start_city, start_mask)

if path is None:
    print("No valid path found")
else:
    s = [0] * 15
    s[0] = 1
    s[14] = 1
    for i in range(1, 12):
        s[i] = 1
    s[12] = 0
    s[13] = 0

    current_day = 1
    itinerary = []
    itinerary.append(f"Day {current_day}: Stay in {path[0]}")
    current_day += 1

    for i in range(1, len(path)):
        itinerary.append(f"Day {current_day}: Fly from {path[i-1]} to {path[i]}")
        current_day += 1
        if s[i] > 0:
            for j in range(s[i]):
                itinerary.append(f"Day {current_day}: Stay in {path[i]}")
                current_day += 1

    for line in itinerary:
        print(line)