import json
from itertools import permutations

def find_valid_itinerary():
    cities = ['Geneva', 'Munich', 'Valencia', 'Bucharest', 'Stuttgart']
    stay_durations = {
        'Geneva': 4,
        'Munich': 7,
        'Valencia': 6,
        'Bucharest': 2,
        'Stuttgart': 2
    }
    constraints = {
        'Geneva': (1, 4),
        'Munich': (4, 10)
    }
    direct_flights = {
        'Geneva': ['Munich', 'Valencia'],
        'Munich': ['Geneva', 'Valencia', 'Bucharest'],
        'Valencia': ['Geneva', 'Munich', 'Bucharest', 'Stuttgart'],
        'Bucharest': ['Valencia', 'Munich'],
        'Stuttgart': ['Valencia']
    }

    # Generate all possible permutations of the cities
    for perm in permutations(cities):
        itinerary = []
        current_day = 1
        valid = True
        prev_city = None
        
        for city in perm:
            duration = stay_durations[city]
            day_range_start = current_day
            day_range_end = current_day + duration - 1
            
            # Check constraints
            if city in constraints:
                constr_start, constr_end = constraints[city]
                if not (day_range_start <= constr_end and day_range_end >= constr_start):
                    valid = False
                    break
            
            # Check flight connection
            if prev_city is not None:
                if city not in direct_flights[prev_city]:
                    valid = False
                    break
                itinerary.append({
                    'flying': f'Day {current_day-1}-{current_day-1}',
                    'from': prev_city,
                    'to': city
                })
            
            itinerary.append({
                'day_range': f'Day {day_range_start}-{day_range_end}',
                'place': city
            })
            current_day += duration
            prev_city = city
        
        # Check total days
        if valid and current_day - 1 == 17:
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