from collections import defaultdict

def find_itinerary(flights):
    flight_dict = defaultdict(list)
    for flight in flights:
        dep_city, arr_city, flight_number, dep_day = flight
        if 1 <= dep_day <= 15:
            flight_dict[(dep_city, dep_day)].append((arr_city, flight_number))
    
    stack = []
    start_visited = frozenset(['TYO'])
    stack.append(('TYO', 1, start_visited, []))
    
    memo = set()
    
    while stack:
        current_city, day, visited, path = stack.pop()
        if day == 16:
            return path
        state_key = (current_city, visited)
        if state_key in memo:
            continue
        memo.add(state_key)
        
        flights_key = (current_city, day)
        if flights_key in flight_dict:
            for next_flight in flight_dict[flights_key]:
                arr_city, flight_num = next_flight
                if arr_city in visited:
                    continue
                new_visited = visited | {arr_city}
                new_path = path + [flight_num]
                stack.append((arr_city, day + 1, new_visited, new_path))
    
    return "No solution found"

flights = [
    # Flight data would be inserted here
]

itinerary = find_itinerary(flights)
if isinstance(itinerary, list):
    print(itinerary)
else:
    print(itinerary)