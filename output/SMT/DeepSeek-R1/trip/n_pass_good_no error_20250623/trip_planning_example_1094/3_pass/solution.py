from collections import defaultdict

def find_itinerary(flights):
    flight_dict = defaultdict(list)
    for flight in flights:
        dep_city, arr_city, flight_number, dep_day = flight
        if 1 <= dep_day <= 15:
            flight_dict[(dep_city, dep_day)].append((arr_city, flight_number))
    
    dp = [dict() for _ in range(17)]
    start_visited = frozenset(['TYO'])
    start_state = ('TYO', start_visited)
    dp[1][start_state] = (None, None)
    
    for day in range(1, 16):
        for state in list(dp[day].keys()):
            current_city, visited = state
            key = (current_city, day)
            if key in flight_dict:
                for arr_city, flight_number in flight_dict[key]:
                    if arr_city in visited:
                        continue
                    new_visited = visited | {arr_city}
                    new_visited_frozen = frozenset(new_visited)
                    new_state = (arr_city, new_visited_frozen)
                    if new_state not in dp[day+1]:
                        dp[day+1][new_state] = (state, flight_number)
    
    if not dp[16]:
        return "No solution found"
    
    state = next(iter(dp[16].keys()))
    path = []
    current_state = state
    for d in range(16, 1, -1):
        parent_state, flight_number = dp[d][current_state]
        path.append(flight_number)
        current_state = parent_state
    path.reverse()
    return path

flights = [
    # Flight data would be inserted here
]

itinerary = find_itinerary(flights)
if isinstance(itinerary, list):
    print(itinerary)
else:
    print(itinerary)