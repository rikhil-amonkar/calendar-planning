import json
from itertools import permutations

def main():
    # Cities and their required days
    cities = {
        'Bucharest': 2,
        'Krakow': 4,
        'Munich': 3,
        'Barcelona': 5,
        'Warsaw': 5,
        'Budapest': 5,
        'Stockholm': 2,
        'Riga': 5,
        'Edinburgh': 5,
        'Vienna': 5
    }
    
    # Fixed events
    fixed_events = [
        {'city': 'Munich', 'day_range': (18, 20)},
        {'city': 'Warsaw', 'day_range': (25, 29)},
        {'city': 'Budapest', 'day_range': (9, 13)},
        {'city': 'Stockholm', 'day_range': (17, 18)},
        {'city': 'Edinburgh', 'day_range': (1, 5)}
    ]
    
    # Direct flights
    direct_flights = {
        'Budapest': ['Munich', 'Vienna', 'Edinburgh', 'Barcelona', 'Warsaw', 'Bucharest'],
        'Bucharest': ['Riga', 'Munich', 'Warsaw', 'Vienna', 'Barcelona', 'Budapest'],
        'Munich': ['Budapest', 'Krakow', 'Warsaw', 'Bucharest', 'Barcelona', 'Stockholm', 'Edinburgh', 'Vienna'],
        'Krakow': ['Munich', 'Warsaw', 'Edinburgh', 'Stockholm', 'Vienna', 'Barcelona'],
        'Barcelona': ['Warsaw', 'Munich', 'Stockholm', 'Edinburgh', 'Riga', 'Budapest', 'Bucharest', 'Vienna', 'Krakow'],
        'Warsaw': ['Munich', 'Barcelona', 'Krakow', 'Bucharest', 'Vienna', 'Budapest', 'Riga', 'Stockholm'],
        'Stockholm': ['Edinburgh', 'Krakow', 'Munich', 'Barcelona', 'Riga', 'Vienna', 'Warsaw'],
        'Riga': ['Bucharest', 'Barcelona', 'Edinburgh', 'Vienna', 'Munich', 'Warsaw', 'Stockholm'],
        'Edinburgh': ['Stockholm', 'Krakow', 'Barcelona', 'Budapest', 'Munich', 'Riga'],
        'Vienna': ['Budapest', 'Riga', 'Krakow', 'Bucharest', 'Munich', 'Barcelona', 'Stockholm', 'Warsaw']
    }
    
    # Initialize itinerary
    itinerary = []
    
    # Add fixed events to itinerary
    for event in fixed_events:
        start, end = event['day_range']
        itinerary.append({'day_range': f'Day {start}-{end}', 'place': event['city']})
    
    # Determine remaining cities and days
    remaining_cities = {city: days for city, days in cities.items()}
    for event in fixed_events:
        city = event['city']
        start, end = event['day_range']
        duration = end - start + 1
        remaining_cities[city] -= duration
    
    # Remove cities with zero remaining days
    remaining_cities = {city: days for city, days in remaining_cities.items() if days > 0}
    
    # Function to check if two cities are connected
    def is_connected(city1, city2):
        return city2 in direct_flights.get(city1, [])
    
    # Generate possible orderings of remaining cities
    remaining_city_list = list(remaining_cities.keys())
    
    # Try all permutations (not optimal for large n, but n is small here)
    for perm in permutations(remaining_city_list):
        valid = True
        temp_itinerary = []
        current_city = None
        
        # Check if the permutation is feasible
        for i, city in enumerate(perm):
            if i == 0:
                # First city must be connected to one of the fixed cities
                connected = False
                for fixed in fixed_events:
                    if is_connected(fixed['city'], city):
                        connected = True
                        break
                if not connected:
                    valid = False
                    break
            else:
                if not is_connected(perm[i-1], city):
                    valid = False
                    break
        
        if not valid:
            continue
        
        # If permutation is valid, assign days
        day = 1
        temp_itinerary = []
        
        # Add fixed events first
        for event in fixed_events:
            start, end = event['day_range']
            temp_itinerary.append({'day_range': f'Day {start}-{end}', 'place': event['city']})
        
        # Assign remaining cities
        for city in perm:
            days_needed = remaining_cities[city]
            # Find earliest available days
            assigned = False
            for d in range(1, 33 - days_needed + 1):
                overlap = False
                for event in temp_itinerary:
                    event_start, event_end = map(int, event['day_range'].split('Day ')[1].split('-'))
                    if not (d + days_needed - 1 < event_start or d > event_end):
                        overlap = True
                        break
                if not overlap:
                    temp_itinerary.append({'day_range': f'Day {d}-{d + days_needed - 1}', 'place': city})
                    assigned = True
                    break
            if not assigned:
                valid = False
                break
        
        if valid:
            # Sort itinerary by day
            temp_itinerary.sort(key=lambda x: int(x['day_range'].split('Day ')[1].split('-')[0]))
            itinerary = temp_itinerary
            break
    
    # Output the itinerary
    print(json.dumps({'itinerary': itinerary}, indent=2))

if __name__ == "__main__":
    main()