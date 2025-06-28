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

def is_valid_itinerary(seq):
    if seq[0] != 'Brussels':
        return False
    current_day = 1
    venice_start = None
    madrid_start = None
    reykjavik_index = None
    london_index = None
    madrid_index = None
    santorini_index = None
    
    for i, city in enumerate(seq):
        if city == 'Venice':
            venice_start = current_day
        elif city == 'Madrid':
            madrid_start = current_day
            madrid_index = i
        elif city == 'Reykjavik':
            reykjavik_index = i
        elif city == 'London':
            london_index = i
        elif city == 'Santorini':
            santorini_index = i
        
        current_day += durations[city]
    
    if venice_start is None or madrid_start is None or reykjavik_index is None or london_index is None or santorini_index is None:
        return False
        
    if not (3 <= venice_start <= 7):
        return False
    if not (3 <= madrid_start <= 11):
        return False
    if not (reykjavik_index < santorini_index):
        return False
    if not (london_index < madrid_index < santorini_index):
        return False
    
    return True

def dfs(current, visited, path, start_day, total_days):
    if len(path) == 7:
        if start_day - 1 == total_days and is_valid_itinerary(path):
            return path
        return None
    
    for next_city in graph[current]:
        if next_city not in visited:
            new_visited = visited | {next_city}
            new_start_day = start_day + durations[current]
            new_path = path + [next_city]
            result = dfs(next_city, new_visited, new_path, new_start_day, total_days)
            if result:
                return result
    return None

def main():
    total_days = 17
    start_city = 'Brussels'
    result_path = dfs(start_city, {start_city}, [start_city], 1, total_days)
    
    if result_path:
        itinerary = format_itinerary(result_path)
        print(json.dumps({"itinerary": itinerary}))
    else:
        print(json.dumps({"error": "No valid itinerary found"}))

if __name__ == '__main__':
    main()