import json
from itertools import permutations

def find_itinerary():
    # Define constraints
    total_days = 12
    city_days = {
        'Hamburg': 2,
        'Zurich': 3,  # Fixed spelling to match flight list
        'Helsinki': 2,
        'Bucharest': 2,
        'Split': 3
    }
    cities = list(city_days.keys())
    wedding_constraint = (1, 3)  # Wedding in Zurich between day 1 and day 3
    conference_days = {4, 10}  # Conference in Split on day 4 and day 10
    
    # Define direct flights as adjacency list
    direct_flights = {
        'Zurich': ['Helsinki', 'Hamburg', 'Bucharest', 'Split'],
        'Helsinki': ['Zurich', 'Hamburg', 'Split'],  # Fixed spelling
        'Hamburg': ['Zurich', 'Helsinki', 'Bucharest', 'Split'],  # Fixed spelling
        'Bucharest': ['Zurich', 'Hamburg'],
        'Split': ['Zurich', 'Helsinki', 'Hamburg']
    }
    
    # Generate all possible permutations of the cities
    for perm in permutations(cities):
        # Try to assign days according to the permutation
        day = 1
        valid = True
        temp_itinerary = []
        remaining_days = city_days.copy()
        remaining_conf_days = conference_days.copy()
        wedding_satisfied = False
        
        for i, city in enumerate(perm):
            if i > 0:
                prev_city = perm[i-1]
                if city not in direct_flights.get(prev_city, []):
                    valid = False
                    break
            
            # Assign days to the city
            days_needed = remaining_days[city]
            start_day = day
            end_day = day + days_needed - 1
            
            # Check if this exceeds total days
            if end_day > total_days:
                valid = False
                break
            
            # Check wedding constraint
            if city == 'Zurich':
                wedding_days = set(range(start_day, end_day+1))
                if wedding_days.intersection(range(wedding_constraint[0], wedding_constraint[1]+1)):
                    wedding_satisfied = True
            
            # Check conference constraints
            if city == 'Split':
                visit_days = set(range(start_day, end_day+1))
                for conf_day in list(remaining_conf_days):
                    if conf_day in visit_days:
                        remaining_conf_days.remove(conf_day)
            
            temp_itinerary.append({
                'day_range': f"Day {start_day}-{end_day}",
                'place': city
            })
            day = end_day + 1
            remaining_days[city] = 0
        
        # Check all constraints
        if (valid and day - 1 == total_days 
            and all(v == 0 for v in remaining_days.values())
            and len(remaining_conf_days) == 0
            and wedding_satisfied):
            return {"itinerary": temp_itinerary}
    
    return {"itinerary": []}

# Execute and print the result
result = find_itinerary()
print(json.dumps(result, indent=2))