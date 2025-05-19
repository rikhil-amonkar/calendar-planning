import json

# Define the fixed periods
fixed_periods = {
    'Lisbon': {'start_day': 4, 'end_day': 5, 'duration': 2},
    'Dubrovnik': {'start_day': 6, 'end_day': 10, 'duration': 5},
    'Copenhagen': {'start_day': 11, 'end_day': 15, 'duration': 5},
    'Prague': {'start_day': 17, 'end_day': 19, 'duration': 3},
    'Tallinn': {'start_day': 1, 'end_day': 2, 'duration': 2},
    'Stockholm': {'start_day': 13, 'end_day': 16, 'duration': 4},
    'Split': {'start_day': 21, 'end_day': 23, 'duration': 3},
    'Lyon': {'start_day': 18, 'end_day': 19, 'duration': 2}
}

# Define the other cities with their required durations
other_cities = {
    'Amsterdam': 0,
    'Barcelona': 0,
    'Florence': 0,
    'Marseille': 0,
    'Paris': 0,
    'Rome': 0,
    'Venice': 0,
    'Vienna': 0
}

# Flight connections (city_to_city: from -> to)
flight_connections = {
    'Tallinn': ['Copenhagen'],
    'Copenhagen': ['Stockholm', 'Split'],
    'Stockholm': ['Copenhagen', 'Split', 'Prague'],
    'Split': ['Copenhagen', 'Lyon'],
    'Lisbon': ['Copenhagen', 'Lyon'],
    'Dubrovnik': ['Stockholm'],
    'Prague': ['Split', 'Lyon'],
    'Lyon': ['Copenhagen', 'Split']
}

def compute_itinerary():
    # Initialize variables
    current_day = 1
    current_city = 'Tallinn'
    visited = {'Tallinn': True}
    itinerary = []

    # Backtracking function
    def backtrack():
        nonlocal current_day, current_city, visited, itinerary
        if current_day > 19:
            return False
        if all(visited[city] for city in other_cities):
            return True
        for next_city in flight_connections.get(current_city, []):
            if next_city not in visited and is_valid_transition(current_city, next_city):
                visited[next_city] = True
                new_day = current_day + 1
                if (fixed_periods.get(next_city, {}).get('start_day') <= new_day <= 
                    fixed_periods.get(next_city, {}).get('end_day')):
                    if next_city in other_cities and other_cities[next_city] > 0:
                        if (fixed_periods.get(next_city, {}).get('start_day') <= new_day <= 
                            fixed_periods.get(next_city, {}).get('end_day')):
                            itinerary.append({'day_range': f'Day {new_day}', 'place': next_city})
                            if backtrack():
                                return True
                            itinerary.pop()
                elif next_city in fixed_periods:
                    if fixed_periods[next_city]['start_day'] <= new_day <= fixed_periods[next_city]['end_day']:
                        itinerary.append({'day_range': f'Day {new_day}', 'place': next_city})
                        if backtrack():
                            return True
                        itinerary.pop()
                else:
                    if new_day + other_cities.get(next_city, 0) <= 19:
                        itinerary.append({'day_range': f'Day {new_day}', 'place': next_city})
                        if backtrack():
                            return True
                        itinerary.pop()
        return False

    # Helper functions
    def is_valid_transition(from_city, to_city):
        return to_city in flight_connections.get(from_city, [])

    def is_valid_duration(city, day):
        if city in fixed_periods:
            fp = fixed_periods[city]
            return fp['start_day'] <= day <= fp['end_day']
        else:
            return True

    # Start backtracking from Tallinn
    if backtrack():
        return json.dumps([c for c in itinerary])
    else:
        return json.dumps([])

# Run the function and print the result
result = compute_itinerary()
print(result)