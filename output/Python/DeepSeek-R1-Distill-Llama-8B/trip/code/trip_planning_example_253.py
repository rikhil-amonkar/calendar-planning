import json

# Define the fixed periods
fixed_periods = {
    'Amsterdam': {'start_day': 9, 'end_day': 11, 'duration': 3},
    'Lyon': {'start_day': 7, 'end_day': 9, 'duration': 3},
    'Vienna': {'start_day': 1, 'end_day': 7, 'duration': 7},
    'Santorini': {'start_day': 10, 'end_day': 14, 'duration': 4}
}

# Define the other cities with their required durations
other_cities = {
    'Amsterdam': 3,
    'Vienna': 7,
    'Santorini': 4,
    'Lyon': 3
}

# Flight connections (city_to_city: from -> to)
flight_connections = {
    'Amsterdam': ['Vienna', 'Santorini'],
    'Vienna': ['Amsterdam', 'Lyon'],
    'Lyon': ['Amsterdam'],
    'Santorini': ['Amsterdam', 'Vienna']
}

def compute_itinerary():
    # Initialize variables
    current_day = 1
    current_city = 'Amsterdam'
    visited = {'Amsterdam': True}
    itinerary = []

    # Backtracking function
    def backtrack():
        nonlocal current_day, current_city, visited, itinerary
        if current_day > 14:
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
                    if new_day + other_cities.get(next_city, 0) <= 14:
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

    # Start backtracking from Amsterdam
    if backtrack():
        return json.dumps([c for c in itinerary])
    else:
        return json.dumps([])

# Run the function and print the result
result = compute_itinerary()
print(result)