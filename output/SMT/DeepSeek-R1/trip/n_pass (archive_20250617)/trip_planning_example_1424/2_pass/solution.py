from collections import deque

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
    'Reykjavik': ['Helsinki'],
    'Split': ['Lyon', 'Warsaw'],
    'Stockholm': ['Athens', 'Helsinki', 'Prague'],
    'Valencia': ['Athens', 'Dublin', 'Lyon', 'Munich', 'Naples', 'Porto'],
    'Warsaw': ['Munich', 'Naples', 'Prague', 'Split']
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
queue = deque()
start_mask = 1 << start_index
queue.append((start_city, start_mask, [start_city]))
visited_states = set()
visited_states.add((start_city, start_mask))

path_found = None

while queue:
    current, mask, path = queue.popleft()
    if current == end_city and mask == all_done:
        path_found = path
        break
    for neighbor in graph[current]:
        idx = city_to_index[neighbor]
        if mask & (1 << idx):
            continue
        new_mask = mask | (1 << idx)
        state = (neighbor, new_mask)
        if state not in visited_states:
            visited_states.add(state)
            new_path = path + [neighbor]
            queue.append((neighbor, new_mask, new_path))

if path_found is None:
    print("No valid path found")
else:
    s = [0] * n
    s[0] = 1
    s[14] = 1
    total_needed = 13 - 1 - 1
    for i in range(1, 14):
        if total_needed > 0:
            s[i] = 1
            total_needed -= 1
        else:
            s[i] = 0

    current_day = 1
    itinerary = []
    itinerary.append(f"Day {current_day}: Stay in {path_found[0]}")
    current_day += 1

    for i in range(1, len(path_found)):
        itinerary.append(f"Day {current_day}: Fly from {path_found[i-1]} to {path_found[i]}")
        current_day += 1
        if s[i] > 0:
            for j in range(s[i]):
                itinerary.append(f"Day {current_day}: Stay in {path_found[i]}")
                current_day += 1

    for line in itinerary:
        print(line)