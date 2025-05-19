import json
from itertools import permutations

def find_itinerary():
    # Input parameters
    total_days = 18
    city_stays = {
        'Reykjavik': 4,
        'Riga': 2,
        'Oslo': 3,
        'Lyon': 5,
        'Dubrovnik': 2,
        'Madrid': 2,
        'Warsaw': 4,
        'London': 3
    }
    
    # Constraints
    constraints = [
        ('Riga', 4, 5),
        ('Dubrovnik', 7, 8)
    ]
    
    # Direct flights
    direct_flights = {
        'Warsaw': ['Reykjavik', 'Riga', 'London', 'Madrid', 'Oslo'],
        'Oslo': ['Madrid', 'Dubrovnik', 'Reykjavik', 'Riga', 'Lyon', 'London', 'Warsaw'],
        'Riga': ['Warsaw', 'Oslo'],
        'Lyon': ['London', 'Madrid', 'Oslo'],
        'Madrid': ['Oslo', 'London', 'Lyon', 'Dubrovnik', 'Warsaw', 'Reykjavik'],
        'Dubrovnik': ['Oslo', 'Madrid'],
        'London': ['Lyon', 'Madrid', 'Warsaw', 'Oslo', 'Reykjavik'],
        'Reykjavik': ['Warsaw', 'Madrid', 'Oslo', 'London']
    }
    
    # Generate all possible permutations of cities
    cities = list(city_stays.keys())
    
    # Function to check if a permutation is valid
    def is_valid_permutation(perm):
        # Check all flights are direct
        for i in range(len(perm) - 1):
            if perm[i+1] not in direct_flights[perm[i]]:
                return False
        return True
    
    # Find all valid permutations
    valid_perms = []
    for perm in permutations(cities):
        if is_valid_permutation(perm):
            valid_perms.append(perm)
    
    # Function to check if constraints are satisfied
    def satisfies_constraints(itinerary):
        for city, start_day, end_day in constraints:
            found = False
            current_day = 1
            for entry in itinerary:
                if 'place' in entry:
                    place = entry['place']
                    day_range = entry['day_range']
                    day_start = int(day_range.split('-')[0].split(' ')[1])
                    day_end = int(day_range.split('-')[1])
                    if place == city:
                        if not (day_start <= start_day and day_end >= end_day):
                            return False
                        found = True
                current_day = day_end + 1
            if not found:
                return False
        return True
    
    # Try all valid permutations to find a valid itinerary
    for perm in valid_perms:
        itinerary = []
        current_day = 1
        remaining_cities = list(perm)
        
        while remaining_cities and current_day <= total_days:
            city = remaining_cities.pop(0)
            stay_days = city_stays[city]
            day_end = current_day + stay_days - 1
            
            if day_end > total_days:
                break  # Not enough days left
            
            if itinerary:
                last_entry = itinerary[-1]
                if 'place' in last_entry:
                    from_city = last_entry['place']
                    itinerary.append({
                        'flying': f'Day {current_day-1}-{current_day-1}',
                        'from': from_city,
                        'to': city
                    })
            
            itinerary.append({
                'day_range': f'Day {current_day}-{day_end}',
                'place': city
            })
            
            current_day = day_end + 1
        
        if len(itinerary) > 0 and current_day > total_days and satisfies_constraints(itinerary):
            return itinerary
    
    return None

# Find and print the itinerary
itinerary = find_itinerary()
if itinerary:
    print(json.dumps(itinerary, indent=2))
else:
    print(json.dumps({"error": "No valid itinerary found"}, indent=2))