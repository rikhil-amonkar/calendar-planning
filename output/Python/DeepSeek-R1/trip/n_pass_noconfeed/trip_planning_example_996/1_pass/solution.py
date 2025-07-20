import json

cities = {
    'Mykonos': 3,
    'Zurich': 5,
    'Prague': 3,
    'Valencia': 5,
    'Bucharest': 5,
    'Riga': 5,
    'Nice': 2
}

connections = {
    'Mykonos': ['Nice', 'Zurich'],
    'Nice': ['Mykonos', 'Riga', 'Zurich'],
    'Zurich': ['Mykonos', 'Prague', 'Bucharest', 'Valencia', 'Riga', 'Nice'],
    'Prague': ['Bucharest', 'Zurich', 'Riga', 'Valencia'],
    'Valencia': ['Bucharest', 'Zurich', 'Prague'],
    'Bucharest': ['Prague', 'Valencia', 'Zurich', 'Riga'],
    'Riga': ['Nice', 'Bucharest', 'Prague', 'Zurich']
}

def dfs(current_city, arrival_day, visited, itinerary_so_far):
    dur = cities[current_city]
    departure_day = arrival_day + dur - 1
    
    if current_city == 'Prague':
        if not (arrival_day <= 9 and departure_day >= 7):
            return None
    
    if len(visited) == 6:
        if departure_day == 22:
            full_itinerary = itinerary_so_far + [(arrival_day, departure_day, current_city)]
            return full_itinerary
        else:
            return None
    
    new_visited = visited | {current_city}
    
    for next_city in connections[current_city]:
        if next_city not in new_visited:
            next_arrival = departure_day
            dur_next = cities[next_city]
            next_departure = next_arrival + dur_next - 1
            if next_departure > 22:
                continue
                
            if next_city == 'Prague':
                if not (next_arrival <= 9 and next_departure >= 7):
                    continue
                    
            new_itinerary = itinerary_so_far + [(arrival_day, departure_day, current_city)]
            res = dfs(next_city, next_arrival, new_visited, new_itinerary)
            if res is not None:
                return res
                
    return None

def main():
    start_city = 'Mykonos'
    start_day = 1
    visited = set()
    itinerary_so_far = []
    result_itinerary = dfs(start_city, start_day, visited, itinerary_so_far)
    
    if result_itinerary is None:
        print(json.dumps({"itinerary": []}))
        return
        
    output_list = []
    for (start, end, city) in result_itinerary:
        day_range_str = f"Day {start}-{end}"
        output_list.append({"day_range": day_range_str, "place": city})
        
    result_dict = {"itinerary": output_list}
    print(json.dumps(result_dict))

if __name__ == "__main__":
    main()