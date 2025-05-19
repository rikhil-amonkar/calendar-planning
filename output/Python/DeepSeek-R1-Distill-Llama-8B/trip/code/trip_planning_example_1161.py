import json

# Define the fixed periods
fixed_periods = {
    'Mykonos': {'start_day': 15, 'end_day': 18, 'duration': 4},
    'Krakow': {'start_day': 6, 'end_day': 10, 'duration': 5},
    'Vilnius': {'start_day': 12, 'end_day': 13, 'duration': 2},
    'Helsinki': {'start_day': 3, 'end_day': 4, 'duration': 2},
    'Dubrovnik': {'start_day': 2, 'end_day': 4, 'duration': 3},
    'Oslo': {'start_day': 1, 'end_day': 2, 'duration': 2},
    'Madrid': {'start_day': 14, 'end_day': 17, 'duration': 5},
    'Paris': {'start_day': 16, 'end_day': 17, 'duration': 2}
}

# Define the other cities with their required durations
other_cities = {
    'Amsterdam': 0,
    'Barcelona': 0,
    'Berlin': 0,
    'Brussels': 0,
    'Cologne': 0,
    'Florence': 0,
    'Rome': 0,
    'Vienna': 0
}

# Flight connections (city_to_city: from -> to)
flight_connections = {
    'Oslo': ['Krakow', 'Paris', 'Madrid'],
    'Krakow': ['Oslo', 'Vilnius'],
    'Vilnius': ['Paris'],
    'Helsinki': ['Dubrovnik', 'Madrid'],
    'Dubrovnik': ['Oslo', 'Madrid'],
    'Madrid': ['Mykonos', 'Paris'],
    'Mykonos': ['Oslo'],
    'Paris': ['Madrid', 'Vilnius']
}

def compute_itinerary():
    # Initialize variables
    current_day = 1
    current_city = 'Oslo'
    visited = {'Oslo': True}
    itinerary = []

    # Backtracking function
    def backtrack():
        nonlocal current_day, current_city, visited, itinerary
        if current_day > 18:
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
                    if new_day + other_cities.get(next_city, 0) <= 18:
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

    # Start backtracking from Oslo
    if backtrack():
        return json.dumps([c for c in itinerary])
    else:
        return json.dumps([])

# Run the function and print the result
result = compute_itinerary()
print(result)