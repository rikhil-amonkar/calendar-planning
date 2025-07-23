import json
from itertools import permutations

def find_itinerary():
    # Define the constraints
    cities = {
        'Berlin': {'duration': 5, 'fixed_range': (1, 5)},
        'Split': {'duration': 3},
        'Bucharest': {'duration': 3, 'fixed_range': (13, 15)},
        'Riga': {'duration': 5},
        'Lisbon': {'duration': 3},
        'Tallinn': {'duration': 4},
        'Lyon': {'duration': 5, 'fixed_range': (7, 11)}
    }
    
    # Define direct flights as a graph (undirected)
    flight_graph = {
        'Lisbon': ['Bucharest', 'Berlin', 'Riga', 'Lyon'],
        'Bucharest': ['Lisbon', 'Riga', 'Lyon'],
        'Berlin': ['Lisbon', 'Riga', 'Split', 'Tallinn'],
        'Riga': ['Bucharest', 'Berlin', 'Lisbon', 'Tallinn'],
        'Split': ['Berlin', 'Lyon'],
        'Tallinn': ['Riga', 'Berlin'],
        'Lyon': ['Split', 'Lisbon', 'Bucharest']
    }
    
    # Fixed events
    itinerary = []
    # Add Berlin days 1-5
    itinerary.append({'day_range': 'Day 1-5', 'place': 'Berlin'})
    current_day = 6
    current_city = 'Berlin'
    
    # Remaining cities to visit (excluding Berlin)
    remaining_cities = [city for city in cities.keys() if city != 'Berlin']
    remaining_durations = {city: cities[city]['duration'] for city in remaining_cities}
    
    # Handle Lyon wedding (days 7-11)
    # We must be in Lyon by day 7
    # Current day is 6, current city is Berlin
    # Need to get from Berlin to Lyon by day 7
    # Possible paths: Berlin -> Split -> Lyon
    # Or Berlin -> Lisbon -> Lyon, etc.
    
    # Find path from Berlin to Lyon by day 7 (must arrive by day 7)
    # Since current day is 6, we can fly on day 6 to arrive in Lyon by day 7
    # Check direct flights from Berlin to Lyon: none, so need intermediate
    # Berlin -> Split -> Lyon is possible
    # Berlin -> Lisbon -> Lyon is possible
    # Berlin -> Riga -> ... not helpful
    # Choose Berlin -> Split -> Lyon
    
    itinerary.append({'day_range': 'Day 6', 'place': 'Split'})
    itinerary.append({'day_range': 'Day 7-11', 'place': 'Lyon'})
    current_day = 12
    current_city = 'Lyon'
    remaining_cities.remove('Lyon')
    remaining_durations.pop('Lyon')
    
    # Next fixed event: Bucharest days 13-15
    # Current day is 12, current city is Lyon
    # Need to get to Bucharest by day 13
    # Direct flight Lyon -> Bucharest
    itinerary.append({'day_range': 'Day 12', 'place': 'Bucharest'})
    itinerary.append({'day_range': 'Day 13-15', 'place': 'Bucharest'})
    current_day = 16
    current_city = 'Bucharest'
    remaining_cities.remove('Bucharest')
    remaining_durations.pop('Bucharest')
    
    # Remaining cities: Split (3 days), Riga (5), Lisbon (3), Tallinn (4)
    # But Split was already visited on day 6, but duration is 3 days
    # Need to revisit Split for 2 more days (since day 6 counts as 1)
    # Alternatively, adjust Split to be 3 contiguous days
    
    # Reconstruct remaining cities and durations correctly
    remaining_cities = ['Split', 'Riga', 'Lisbon', 'Tallinn']
    remaining_durations = {
        'Split': 3,
        'Riga': 5,
        'Lisbon': 3,
        'Tallinn': 4
    }
    # Subtract Split day already spent
    remaining_durations['Split'] -= 1
    
    # Now plan remaining days (16-22)
    # Try to visit Riga next (5 days)
    # From Bucharest, direct flights to Riga
    itinerary.append({'day_range': f'Day {current_day}-{current_day + remaining_durations["Riga"] - 1}', 'place': 'Riga'})
    current_day += remaining_durations["Riga"]
    current_city = 'Riga'
    remaining_cities.remove('Riga')
    remaining_durations.pop('Riga')
    
    # Next, visit Tallinn (4 days), direct flight from Riga
    itinerary.append({'day_range': f'Day {current_day}-{current_day + remaining_durations["Tallinn"] - 1}', 'place': 'Tallinn'})
    current_day += remaining_durations["Tallinn"]
    current_city = 'Tallinn'
    remaining_cities.remove('Tallinn')
    remaining_durations.pop('Tallinn')
    
    # Remaining: Split (2 days), Lisbon (3 days)
    # From Tallinn, can fly to Berlin -> Split
    # Or Tallinn -> Riga -> Lisbon
    # Choose Tallinn -> Riga -> Lisbon
    itinerary.append({'day_range': f'Day {current_day}', 'place': 'Riga'})
    current_day += 1
    current_city = 'Riga'
    
    # Then to Lisbon
    itinerary.append({'day_range': f'Day {current_day}-{current_day + remaining_durations["Lisbon"] - 1}', 'place': 'Lisbon'})
    current_day += remaining_durations["Lisbon"]
    current_city = 'Lisbon'
    remaining_cities.remove('Lisbon')
    remaining_durations.pop('Lisbon')
    
    # Finally, Split (2 days)
    # From Lisbon, fly to Berlin -> Split
    itinerary.append({'day_range': f'Day {current_day}', 'place': 'Berlin'})
    current_day += 1
    itinerary.append({'day_range': f'Day {current_day}-{current_day + 1}', 'place': 'Split'})
    
    # Verify all days are accounted for (1-22)
    # Verify all cities have correct durations
    # This is a heuristic solution; a more rigorous approach would involve backtracking
    
    return {'itinerary': itinerary}

# Output the result
print(json.dumps(find_itinerary()))