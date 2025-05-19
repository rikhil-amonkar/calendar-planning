import json
from itertools import permutations

def find_valid_itinerary():
    # Define the cities and their required days
    cities = {
        'Mykonos': 4,
        'Krakow': 5,
        'Vilnius': 2,
        'Helsinki': 2,
        'Dubrovnik': 3,
        'Oslo': 2,
        'Madrid': 5,
        'Paris': 2
    }
    
    # Define the flight connections
    flight_connections = {
        'Oslo': ['Krakow', 'Paris', 'Madrid', 'Helsinki', 'Dubrovnik', 'Vilnius'],
        'Paris': ['Oslo', 'Madrid', 'Krakow', 'Helsinki', 'Vilnius'],
        'Madrid': ['Paris', 'Dubrovnik', 'Mykonos', 'Oslo', 'Helsinki'],
        'Helsinki': ['Vilnius', 'Oslo', 'Krakow', 'Dubrovnik', 'Paris', 'Madrid'],
        'Dubrovnik': ['Helsinki', 'Madrid', 'Oslo'],
        'Krakow': ['Oslo', 'Paris', 'Helsinki', 'Vilnius'],
        'Vilnius': ['Helsinki', 'Oslo', 'Paris', 'Krakow'],
        'Mykonos': ['Madrid']
    }
    
    # Define constraints
    constraints = [
        {'place': 'Mykonos', 'day_range': (15, 18)},
        {'place': 'Dubrovnik', 'day_range': (2, 4)},
        {'place': 'Oslo', 'day_range': (1, 2)}
    ]
    
    # Generate all possible permutations of the cities
    city_names = list(cities.keys())
    for perm in permutations(city_names):
        itinerary = []
        current_day = 1
        valid = True
        
        # Check if Mykonos is at the end
        if perm[-1] != 'Mykonos':
            continue
        
        # Check if Oslo is first
        if perm[0] != 'Oslo':
            continue
        
        # Check if Dubrovnik is early enough
        if 'Dubrovnik' not in perm[:3]:
            continue
        
        # Try to build the itinerary
        prev_city = None
        day_usage = [0] * 19  # 1-based indexing for days 1-18
        
        for city in perm:
            duration = cities[city]
            
            # Find the earliest start day for this city considering constraints
            start_day = current_day
            if city == 'Mykonos':
                start_day = 15
            elif city == 'Dubrovnik':
                start_day = 2
            elif city == 'Oslo':
                start_day = 1
            
            # Check if the city can fit
            end_day = start_day + duration - 1
            if end_day > 18:
                valid = False
                break
            
            # Check if days are available
            conflict = False
            for day in range(start_day, end_day + 1):
                if day_usage[day] == 1:
                    conflict = True
                    break
            if conflict:
                valid = False
                break
            
            # Mark days as used
            for day in range(start_day, end_day + 1):
                day_usage[day] = 1
            
            # Add flight if not first city
            if prev_city is not None:
                if city not in flight_connections[prev_city]:
                    valid = False
                    break
                itinerary.append({
                    'flying': f'Day {current_day}-{current_day}',
                    'from': prev_city,
                    'to': city
                })
                current_day += 1  # flight day
            
            # Add city stay
            itinerary.append({
                'day_range': f'Day {start_day}-{end_day}',
                'place': city
            })
            current_day = end_day + 1
            prev_city = city
        
        if valid:
            # Verify all constraints are met
            for entry in itinerary:
                if 'day_range' in entry:
                    place = entry['place']
                    day_range = entry['day_range']
                    start, end = map(int, day_range.split('Day ')[1].split('-'))
                    
                    if place == 'Mykonos' and (start != 15 or end != 18):
                        valid = False
                    elif place == 'Dubrovnik' and (start != 2 or end != 4):
                        valid = False
                    elif place == 'Oslo' and (start != 1 or end != 2):
                        valid = False
            
            if valid:
                return itinerary
    
    return None

def main():
    itinerary = find_valid_itinerary()
    if itinerary:
        print(json.dumps(itinerary, indent=2))
    else:
        print(json.dumps({"error": "No valid itinerary found"}, indent=2))

if __name__ == "__main__":
    main()