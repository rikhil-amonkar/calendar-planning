import json
from itertools import permutations

def find_itinerary():
    # Define constraints
    total_days = 12
    city_days = {
        'Hamburg': 2,
        'Zurich': 3,
        'Helsinki': 2,
        'Bucharest': 2,
        'Split': 7
    }
    cities = list(city_days.keys())
    wedding_constraint = (1, 3)  # Wedding in Zurich between day 1 and day 3
    conference_constraints = [(4, 4), (10, 10)]  # Conference in Split on day 4 and day 10
    
    # Define direct flights as adjacency list
    direct_flights = {
        'Zurich': ['Helsinki', 'Hamburg', 'Bucharest', 'Split'],
        'Helsinki': ['Zurich', 'Hamburg', 'Split'],
        'Hamburg': ['Zurich', 'Helsinki', 'Bucharest', 'Split'],
        'Bucharest': ['Zurich', 'Hamburg'],
        'Split': ['Zurich', 'Helsinki', 'Hamburg']
    }
    
    # Correct city name inconsistencies
    direct_flights['Zurich'] = ['Helsinki', 'Hamburg', 'Bucharest', 'Split']
    direct_flights['Zurich'] = direct_flights.pop('Zurich')
    direct_flights['Split'] = ['Zurich', 'Helsinki', 'Hamburg']
    
    # Generate all possible permutations of the cities
    for perm in permutations(cities):
        itinerary = []
        current_perm = list(perm)
        # Check if all cities are present
        if set(current_perm) != set(cities):
            continue
        
        # Try to assign days according to the permutation
        day = 1
        valid = True
        temp_itinerary = []
        remaining_days = city_days.copy()
        
        # Assign Zurich first due to wedding constraint
        if 'Zurich' not in current_perm[:1]:
            continue
        
        for i, city in enumerate(current_perm):
            if i > 0:
                prev_city = current_perm[i-1]
                if city not in direct_flights[prev_city]:
                    valid = False
                    break
            
            # Assign days to the city
            days_needed = remaining_days[city]
            start_day = day
            end_day = day + days_needed - 1
            
            # Check conference constraints for Split
            if city == 'Split':
                conf_days = [conf[0] for conf in conference_constraints]
                if not (start_day <= min(conf_days) <= end_day and start_day <= max(conf_days) <= end_day):
                    valid = False
                    break
            
            # Check wedding constraint for Zurich
            if city == 'Zurich':
                if not (start_day <= wedding_constraint[0] and end_day >= wedding_constraint[1]):
                    valid = False
                    break
            
            temp_itinerary.append({
                'day_range': f"Day {start_day}-{end_day}",
                'place': city
            })
            day = end_day + 1
            remaining_days[city] = 0
        
        # Check if all days are assigned and all constraints are met
        if valid and day - 1 == total_days and all(v == 0 for v in remaining_days.values()):
            itinerary = temp_itinerary
            break
    
    if not itinerary:
        return {"itinerary": []}
    
    return {"itinerary": itinerary}

# Execute and print the result
result = find_itinerary()
print(json.dumps(result))