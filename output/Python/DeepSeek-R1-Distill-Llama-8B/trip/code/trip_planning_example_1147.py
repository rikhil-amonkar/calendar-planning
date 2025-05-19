import json

# Define the fixed periods
fixed_periods = {
    'Istanbul': {'start_day': 1, 'end_day': 5, 'duration': 5},
    'Frankfurt': {'start_day': 16, 'end_day': 18, 'duration': 3},
    'Vilnius': {'start_day': 18, 'end_day': 22, 'duration': 5}
}

# Define the other cities with their required durations
other_cities = {
    'Brussels': 3,
    'Helsinki': 3,
    'Split': 4,
    'Dubrovnik': 2,
    'Milan': 4
}

# Flight connections (city_to_city: from -> to)
flight_connections = {
    'Milan': ['Frankfurt', 'Split', 'Vilnius', 'Brussels'],
    'Split': ['Frankfurt', 'Vilnius'],
    'Brussels': ['Vilnius', 'Helsinki'],
    'Helsinki': ['Vilnius', 'Dubrovnik', 'Frankfurt'],
    'Dubrovnik': ['Frankfurt', 'Istanbul'],
    'Istanbul': ['Brussels', 'Milan', 'Frankfurt'],
    'Frankfurt': ['Vilnius', 'Milan', 'Split'],
    'Vilnius': ['Frankfurt', 'Milan', 'Split']
}

def compute_itinerary():
    # Initialize variables
    current_day = 1
    current_city = 'Istanbul'
    visited = {'Istanbul': True}
    itinerary = []

    # Backtracking function
    def backtrack():
        nonlocal current_day, current_city, visited, itinerary
        if current_day > 22:
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
                            if is_valid_duration(next_city, new_day):
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
                    if new_day + other_cities.get(next_city, 0) <= 22:
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

    # Start backtracking from Istanbul
    if backtrack():
        return json.dumps([c for c in itinerary])
    else:
        return json.dumps([])

# Run the function and print the result
result = compute_itinerary()
print(result)