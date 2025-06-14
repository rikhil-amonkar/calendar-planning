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
full_path = None

for X in ['Valencia', 'Munich', 'Naples']:
    cities_part = set(all_cities) - {X, 'Lyon', 'Split'}
    graph_part = {}
    for city in cities_part:
        graph_part[city] = [n for n in graph[city] if n in cities_part]
    
    n_part = len(cities_part)
    cities_part_list = sorted(cities_part)
    city_to_index_part = {city: idx for idx, city in enumerate(cities_part_list)}
    start_city = 'Porto'
    start_mask = 1 << city_to_index_part[start_city]
    all_done_part = (1 << n_part) - 1

    memo = {}
    def dfs(current, mask):
        if mask == all_done_part:
            return [current]
        key = (current, mask)
        if key in memo:
            return memo[key]
        for neighbor in graph_part[current]:
            idx = city_to_index_part[neighbor]
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

    path_part = dfs(start_city, start_mask)
    if path_part is None:
        continue
    last_city = path_part[-1]
    if last_city in graph[X]:
        full_path = path_part + [X, 'Lyon', 'Split']
        break

if full_path is None:
    print("No valid path found")
else:
    stay_days = []
    for city in full_path:
        if city == X or city == 'Lyon':
            stay_days.append(0)
        else:
            stay_days.append(1)
    
    current_day = 1
    itinerary = []
    itinerary.append(f"Day {current_day}: Stay in {full_path[0]}")
    current_day += 1

    for i in range(1, len(full_path)):
        itinerary.append(f"Day {current_day}: Fly from {full_path[i-1]} to {full_path[i]}")
        current_day += 1
        if stay_days[i] == 1:
            itinerary.append(f"Day {current_day}: Stay in {full_path[i]}")
            current_day += 1

    for line in itinerary:
        print(line)