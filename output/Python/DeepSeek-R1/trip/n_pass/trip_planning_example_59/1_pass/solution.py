import json

def main():
    total_days = 16
    city_durations = {
        'Bucharest': 7,
        'Lyon': 7,
        'Porto': 4
    }
    direct_flights = [('Bucharest', 'Lyon'), ('Lyon', 'Porto')]
    wedding_city = 'Bucharest'
    
    graph = {}
    for a, b in direct_flights:
        graph.setdefault(a, []).append(b)
        graph.setdefault(b, []).append(a)
    
    total_cities = len(city_durations)
    stack = [[wedding_city]]
    path = None
    while stack:
        current_path = stack.pop()
        if len(current_path) == total_cities:
            path = current_path
            break
        last = current_path[-1]
        if last in graph:
            for neighbor in graph[last]:
                if neighbor not in current_path:
                    new_path = current_path + [neighbor]
                    stack.append(new_path)
    
    if path is None:
        result = {"itinerary": []}
        print(json.dumps(result))
        return
    
    current_day = 1
    itinerary_list = []
    for city in path:
        dur = city_durations[city]
        end_day = current_day + dur - 1
        itinerary_list.append({
            "day_range": f"Day {current_day}-{end_day}",
            "place": city
        })
        current_day = end_day
    
    if end_day > total_days:
        result = {"itinerary": []}
    else:
        result = {"itinerary": itinerary_list}
    
    print(json.dumps(result))

if __name__ == '__main__':
    main()