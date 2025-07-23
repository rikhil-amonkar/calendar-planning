import json
from itertools import permutations

def calculate_itinerary():
    # Input parameters
    total_days = 21
    city_days = {
        'Manchester': 3,
        'Istanbul': 7,
        'Venice': 7,
        'Krakow': 6,
        'Lyon': 2
    }
    
    # Constraints
    manchester_wedding = (1, 3)  # Must be in Manchester between day 1 and day 3
    venice_workshop = (3, 9)     # Must be in Venice between day 3 and day 9
    
    # Direct flights
    direct_flights = {
        'Manchester': ['Venice', 'Istanbul', 'Krakow'],
        'Venice': ['Manchester', 'Istanbul', 'Lyon'],
        'Istanbul': ['Manchester', 'Venice', 'Krakow', 'Lyon'],
        'Krakow': ['Istanbul', 'Manchester'],
        'Lyon': ['Venice', 'Istanbul']
    }
    
    # All cities
    cities = list(city_days.keys())
    
    # Generate all possible permutations of the cities
    for perm in permutations(cities):
        # We'll try to build the itinerary with this permutation
        itinerary = []
        remaining_days = city_days.copy()
        current_day = 1
        valid = True
        
        # First assign Manchester (must be first 3 days)
        if remaining_days['Manchester'] > 0:
            start_day = current_day
            end_day = start_day + remaining_days['Manchester'] - 1
            # Check wedding constraint
            if not (start_day <= manchester_wedding[0] and end_day >= manchester_wedding[1]):
                valid = False
                continue
            itinerary.append({
                'day_range': f"Day {start_day}-{end_day}",
                'place': 'Manchester'
            })
            current_day = end_day + 1
            remaining_days['Manchester'] = 0
        
        # Now assign other cities in permutation order, but be more flexible
        prev_city = 'Manchester'
        remaining_cities = [c for c in perm if c != 'Manchester' and remaining_days[c] > 0]
        
        while remaining_cities and valid:
            # Try to find the next city we can fly to from prev_city
            next_city = None
            for city in remaining_cities:
                if city in direct_flights[prev_city]:
                    next_city = city
                    break
            
            if not next_city:
                valid = False
                break
                
            # Assign days to this city
            start_day = current_day
            end_day = start_day + remaining_days[next_city] - 1
            
            # Check Venice workshop constraint
            if next_city == 'Venice':
                if not (start_day <= venice_workshop[1] and end_day >= venice_workshop[0]):
                    valid = False
                    break
            
            itinerary.append({
                'day_range': f"Day {start_day}-{end_day}",
                'place': next_city
            })
            current_day = end_day + 1
            remaining_days[next_city] = 0
            prev_city = next_city
            remaining_cities.remove(next_city)
        
        # Check if all days are assigned and constraints are met
        if valid and current_day - 1 == total_days:
            # Verify all city days are satisfied
            if all(v == 0 for v in remaining_days.values()):
                return {'itinerary': itinerary}
    
    # If no valid itinerary found (though the problem states one exists)
    return {'itinerary': []}

# Calculate and output the itinerary
result = calculate_itinerary()
print(json.dumps(result))