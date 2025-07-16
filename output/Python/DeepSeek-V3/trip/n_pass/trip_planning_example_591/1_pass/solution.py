import json
from itertools import permutations

def find_valid_itinerary():
    # Cities and their required stay durations
    cities = {
        'Stuttgart': 2,
        'Bucharest': 2,
        'Geneva': 4,
        'Valencia': 6,
        'Munich': 7
    }
    
    # Direct flight connections
    connections = {
        'Geneva': ['Munich', 'Valencia'],
        'Munich': ['Geneva', 'Valencia', 'Bucharest'],
        'Valencia': ['Geneva', 'Munich', 'Bucharest', 'Stuttgart'],
        'Bucharest': ['Valencia', 'Munich'],
        'Stuttgart': ['Valencia']
    }
    
    # Constraints
    geneva_constraint = (1, 4)  # Must be in Geneva between day 1 and day 4
    munich_constraint = (4, 10)  # Must be in Munich between day 4 and day 10
    
    # Generate all possible permutations of the cities
    for perm in permutations(cities.keys()):
        # Check if the permutation is a valid path (each consecutive city is connected)
        valid_path = True
        for i in range(len(perm) - 1):
            if perm[i+1] not in connections[perm[i]]:
                valid_path = False
                break
        if not valid_path:
            continue
        
        # Try to assign days to the cities in this order
        itinerary = []
        remaining_days = 17
        current_day = 1
        
        # Assign days to each city in the permutation
        for city in perm:
            duration = cities[city]
            if current_day + duration - 1 > 17:
                valid_path = False
                break
            itinerary.append({
                'day_range': f"Day {current_day}-{current_day + duration - 1}",
                'place': city
            })
            current_day += duration
        
        if not valid_path:
            continue
        
        # Check if the constraints are satisfied
        geneva_ok = False
        munich_ok = False
        for entry in itinerary:
            city = entry['place']
            day_range = entry['day_range']
            start_day = int(day_range.split('-')[0].split(' ')[1])
            end_day = int(day_range.split('-')[1])
            
            if city == 'Geneva':
                # Check if Geneva is visited between day 1 and day 4
                if start_day <= geneva_constraint[1] and end_day >= geneva_constraint[0]:
                    geneva_ok = True
            if city == 'Munich':
                # Check if Munich is visited between day 4 and day 10
                if start_day <= munich_constraint[1] and end_day >= munich_constraint[0]:
                    munich_ok = True
        
        if geneva_ok and munich_ok:
            # Check if all cities are covered with exact durations
            total_days = 0
            city_counts = {}
            for entry in itinerary:
                city = entry['place']
                start_day = int(entry['day_range'].split('-')[0].split(' ')[1])
                end_day = int(entry['day_range'].split('-')[1])
                duration = end_day - start_day + 1
                city_counts[city] = city_counts.get(city, 0) + duration
                total_days += duration
            
            if total_days != 17:
                continue
            
            all_correct = True
            for city, duration in cities.items():
                if city_counts.get(city, 0) != duration:
                    all_correct = False
                    break
            
            if all_correct:
                return {'itinerary': itinerary}
    
    return {'itinerary': []}  # No valid itinerary found

# Execute the function and print the result as JSON
result = find_valid_itinerary()
print(json.dumps(result))