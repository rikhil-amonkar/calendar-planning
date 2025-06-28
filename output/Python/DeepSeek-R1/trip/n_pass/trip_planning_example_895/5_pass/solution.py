import json

graph = {
    'Brussels': ['Venice', 'London', 'Lisbon', 'Reykjavik', 'Madrid'],
    'Venice': ['Madrid', 'Brussels', 'Santorini', 'Lisbon', 'London'],
    'London': ['Brussels', 'Madrid', 'Santorini', 'Reykjavik', 'Lisbon', 'Venice'],
    'Lisbon': ['Reykjavik', 'Venice', 'London', 'Madrid', 'Brussels'],
    'Reykjavik': ['Lisbon', 'Madrid', 'London', 'Brussels'],
    'Santorini': ['Venice', 'London', 'Madrid'],
    'Madrid': ['Venice', 'Reykjavik', 'London', 'Lisbon', 'Santorini', 'Brussels']
}

durations = {
    'Brussels': 2,
    'Venice': 3,
    'London': 3,
    'Lisbon': 4,
    'Reykjavik': 3,
    'Santorini': 3,
    'Madrid': 5
}

def format_itinerary(seq):
    itinerary = []
    current_day = 1
    for city in seq:
        end_day = current_day + durations[city] - 1
        if current_day == end_day:
            day_range = f"Day {current_day}"
        else:
            day_range = f"Day {current_day}-{end_day}"
        itinerary.append({"day_range": day_range, "place": city})
        current_day = end_day + 1
    return itinerary

def dfs(current, visited, path, start_day):
    current_end_day = start_day + durations[current] - 1
    if current_end_day > 23:
        return None
        
    if current == 'Venice':
        if start_day < 3 or start_day > 7:
            return None
    if current == 'Madrid':
        if start_day < 3 or start_day > 11:
            return None

    if len(path) == 7:
        return path

    for next_city in graph[current]:
        if next_city in visited:
            continue

        if next_city == 'Santorini':
            if 'Reykjavik' not in visited or 'Madrid' not in visited:
                continue
        if next_city == 'Madrid':
            if 'London' not in visited:
                continue

        next_start_day = start_day + durations[current]
        next_end_day = next_start_day + durations[next_city] - 1
        if next_end_day > 23:
            continue

        if next_city == 'Venice':
            if next_start_day < 3 or next_start_day > 7:
                continue
        if next_city == 'Madrid':
            if next_start_day < 3 or next_start_day > 11:
                continue

        new_visited = visited | {next_city}
        new_path = path + [next_city]
        result = dfs(next_city, new_visited, new_path, next_start_day)
        if result is not None:
            return result

    return None

def main():
    start_city = 'Brussels'
    result_path = dfs(start_city, {start_city}, [start_city], 1)
    
    if result_path:
        itinerary = format_itinerary(result_path)
        print(json.dumps({"itinerary": itinerary}, indent=2))
    else:
        print(json.dumps({"error": "No valid itinerary found"}))

if __name__ == '__main__':
    main()