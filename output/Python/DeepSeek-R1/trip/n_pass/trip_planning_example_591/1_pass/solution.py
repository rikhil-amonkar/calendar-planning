import json

durations = {
    "Geneva": 4,
    "Munich": 7,
    "Stuttgart": 2,
    "Bucharest": 2,
    "Valencia": 6
}

graph = {
    "Geneva": ["Munich", "Valencia"],
    "Munich": ["Geneva", "Valencia", "Bucharest"],
    "Valencia": ["Munich", "Bucharest", "Stuttgart", "Geneva"],
    "Bucharest": ["Valencia", "Munich"],
    "Stuttgart": ["Valencia"]
}

def dfs(current_end, visited, path, total_days=17):
    if len(path) == 5:
        if path[-1][2] == total_days:
            return path
        return None

    current_city = path[-1][0]
    for neighbor in graph.get(current_city, []):
        if neighbor not in visited:
            start = current_end
            end = start + durations[neighbor] - 1
            if neighbor == "Munich" and start > 10:
                continue
            new_path = path + [(neighbor, start, end)]
            new_visited = visited | {neighbor}
            result = dfs(end, new_visited, new_path, total_days)
            if result is not None:
                return result
    return None

initial_city = "Geneva"
initial_start = 1
initial_end = 4
initial_visited = {initial_city}
initial_path = [(initial_city, initial_start, initial_end)]

result_path = dfs(initial_end, initial_visited, initial_path)

itinerary_list = []
if result_path is not None:
    for (city, start, end) in result_path:
        itinerary_list.append({"day_range": f"Day {start}-{end}", "place": city})
else:
    itinerary_list = []

result_dict = {"itinerary": itinerary_list}
print(json.dumps(result_dict))