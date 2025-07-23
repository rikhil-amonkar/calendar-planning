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
        'Manchester': ['Venice', 'Istanbul', 'Krakow'],  # Note: Fixed typo in 'Venice'
        'Venice': ['Manchester', 'Istanbul', 'Lyon'],
        'Istanbul': ['Manchester', 'Venice', 'Krakow', 'Lyon'],
        'Krakow': ['Istanbul', 'Manchester'],
        'Lyon': ['Venice', 'Istanbul']
    }
    
    # Generate all possible permutations of the cities
    cities = list(city_days.keys())
    
    for perm in permutations(cities):
        # Try to build itinerary with this city order
        itinerary = []
        remaining_days = city_days.copy()
        current_day = 1
        prev_city = None
        valid = True
        
        # Assign cities in permutation order
        for city in perm:
            if remaining_days[city] == 0:
                continue
                
            # Check if we can fly to this city
            if prev_city and city not in direct_flights[prev_city]:
                valid = False
                break
                
            start_day = current_day
            end_day = start_day + remaining_days[city] - 1
            
            # Check constraints
            if city == 'Manchester':
                # Must be in Manchester for days 1-3
                if not (start_day <= 1 and end_day >= 3):
                    valid = False
                    break
            elif city == 'Venice':
                # Must be in Venice for at least some days between 3-9
                if not (start_day <= 9 and end_day >= 3):
                    valid = False
                    break
            
            # Add to itinerary
            itinerary.append({
                'day_range': f"Day {start_day}-{end_day}",
                'place': city
            })
            
            current_day = end_day + 1
            remaining_days[city] = 0
            prev_city = city
            
            # Check if we've exceeded total days
            if current_day - 1 > total_days:
                valid = False
                break
        
        # Check if all days are assigned and all city days used
        if valid and current_day - 1 == total_days and all(v == 0 for v in remaining_days.values()):
            # Additional check for Venice workshop days
            venice_days = [item for item in itinerary if item['place'] == 'Venice'][0]
            venice_start = int(venice_days['day_range'].split('-')[0][4:])
            venice_end = int(venice_days['day_range'].split('-')[1][4:])
            if venice_start > 9 or venice_end < 3:
                continue
            
            return {'itinerary': itinerary}
    
    # If no valid itinerary found
    return {'itinerary': []}

# Calculate and output the itinerary
result = calculate_itinerary()
print(json.dumps(result, indent=2))