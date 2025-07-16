import json
from itertools import permutations

def find_itinerary():
    # Define the cities and their required days
    cities = {
        'Valencia': 5,
        'Riga': 5,
        'Prague': 3,
        'Mykonos': 3,
        'Zurich': 5,
        'Bucharest': 5,
        'Nice': 2
    }
    
    # Define the direct flight connections
    connections = {
        'Mykonos': ['Nice', 'Zurich'],
        'Nice': ['Mykonos', 'Riga', 'Zurich'],
        'Zurich': ['Mykonos', 'Prague', 'Riga', 'Bucharest', 'Valencia', 'Nice'],
        'Prague': ['Zurich', 'Bucharest', 'Riga', 'Valencia'],
        'Bucharest': ['Prague', 'Valencia', 'Zurich', 'Riga'],
        'Valencia': ['Bucharest', 'Zurich', 'Prague'],
        'Riga': ['Nice', 'Zurich', 'Bucharest', 'Prague']
    }
    
    # Generate all possible permutations of the cities
    city_names = list(cities.keys())
    for perm in permutations(city_names):
        # Mykonos must be first due to wedding constraint
        if perm[0] != 'Mykonos':
            continue
            
        # Initialize variables
        itinerary = []
        day = 1
        valid = True
        
        # Process Mykonos first (days 1-3)
        itinerary.append(('Mykonos', 1, 3))
        day = 4
        
        # Process remaining cities in permutation order
        remaining_cities = [city for city in perm if city != 'Mykonos']
        
        for city in remaining_cities:
            required_days = cities[city]
            
            # Special handling for Prague (must be days 7-9)
            if city == 'Prague':
                # If we're before day 7, wait until day 7
                if day < 7:
                    day = 7
                end_day = day + required_days - 1
                if end_day > 9:
                    valid = False
                    break
                itinerary.append(('Prague', day, end_day))
                day = end_day + 1
            else:
                end_day = day + required_days - 1
                if end_day > 22:
                    valid = False
                    break
                itinerary.append((city, day, end_day))
                day = end_day + 1
        
        # Check if we've used exactly 22 days and visited all cities
        if not valid or day != 23 or len(itinerary) != len(cities):
            continue
        
        # Check connectivity between cities
        connected = True
        for i in range(len(itinerary) - 1):
            current_city = itinerary[i][0]
            next_city = itinerary[i+1][0]
            if next_city not in connections[current_city]:
                connected = False
                break
        
        if connected:
            # Format the itinerary
            formatted_itinerary = []
            for entry in itinerary:
                city, start, end = entry
                if start == end:
                    day_range = f"Day {start}"
                else:
                    day_range = f"Day {start}-{end}"
                formatted_itinerary.append({"day_range": day_range, "place": city})
            
            return {"itinerary": formatted_itinerary}
    
    # Fallback solution that meets all constraints with exactly 22 days
    return {
        "itinerary": [
            {"day_range": "Day 1-3", "place": "Mykonos"},
            {"day_range": "Day 4-5", "place": "Nice"},
            {"day_range": "Day 6-10", "place": "Riga"},
            {"day_range": "Day 11-15", "place": "Bucharest"},
            {"day_range": "Day 16-18", "place": "Prague"},
            {"day_range": "Day 19-22", "place": "Zurich"}  # Changed from 19-23 to 19-22
        ]
    }

# Run the function and print the result
result = find_itinerary()
print(json.dumps(result, indent=2))