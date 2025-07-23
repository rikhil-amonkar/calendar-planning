import json
from itertools import permutations

def find_itinerary():
    cities = {
        'Vienna': 4,
        'Milan': 2,
        'Rome': 3,
        'Riga': 2,
        'Lisbon': 3,
        'Vilnius': 4,
        'Oslo': 3
    }
    
    constraints = {
        'Vienna': [(1, 1), (4, 4)],  # Must start on day 1 or day 4
        'Lisbon': [(11, 13)],        # Must be between days 11-13
        'Oslo': [(13, 15)]            # Must be between days 13-15
    }
    
    flight_routes = {
        'Riga': ['Oslo', 'Rome', 'Milan', 'Vienna', 'Lisbon', 'Vilnius'],
        'Oslo': ['Riga', 'Rome', 'Lisbon', 'Milan', 'Vienna', 'Vilnius'],
        'Rome': ['Oslo', 'Riga', 'Lisbon', 'Vienna'],
        'Milan': ['Vienna', 'Riga', 'Oslo', 'Lisbon', 'Vilnius'],
        'Vienna': ['Milan', 'Vilnius', 'Lisbon', 'Riga', 'Rome', 'Oslo'],
        'Vilnius': ['Vienna', 'Oslo', 'Riga', 'Milan'],
        'Lisbon': ['Vienna', 'Oslo', 'Rome', 'Milan', 'Riga']
    }
    
    # Fix typo in flight routes
    flight_routes['Rome'] = ['Oslo', 'Riga', 'Lisbon', 'Vienna']
    flight_routes['Riga'][2] = 'Milan'  # Fix 'Milan' typo
    
    city_list = list(cities.keys())
    
    # Try different starting cities that have constraints
    for start_city in ['Vienna', 'Lisbon', 'Oslo']:
        remaining_cities = [c for c in city_list if c != start_city]
        
        # Try all permutations of remaining cities (with reasonable limit)
        for order in permutations(remaining_cities, min(10, len(remaining_cities))):
            full_order = (start_city,) + order
            itinerary = []
            current_city = None
            remaining_days = cities.copy()
            day = 1
            valid = True
            
            for city in full_order:
                if current_city is None:
                    current_city = city
                else:
                    if city not in flight_routes[current_city]:
                        valid = False
                        break
                    current_city = city
                
                # Check constraints for current city
                if current_city in constraints:
                    constraint_met = False
                    for (start, end) in constraints[current_city]:
                        # Check if the stay overlaps with the constraint period
                        stay_start = day
                        stay_end = day + remaining_days[current_city] - 1
                        if (stay_start <= end and stay_end >= start):
                            constraint_met = True
                            break
                    if not constraint_met:
                        valid = False
                        break
                
                # Allocate days to current city
                days_to_spend = remaining_days[current_city]
                itinerary.append({
                    'day_range': f'Day {day}-{day + days_to_spend - 1}',
                    'place': current_city
                })
                day += days_to_spend
                remaining_days[current_city] = 0
                
                if day > 16:  # Since we want exactly 15 days
                    valid = False
                    break
            
            # Check if all days are used (15) and all cities visited
            if valid and day == 16 and all(days == 0 for days in remaining_days.values()):
                return {"itinerary": itinerary}
    
    # If no solution found with constrained cities first, try all permutations
    for order in permutations(city_list, min(20, len(city_list))):
        itinerary = []
        current_city = None
        remaining_days = cities.copy()
        day = 1
        valid = True
        
        for city in order:
            if current_city is None:
                current_city = city
            else:
                if city not in flight_routes[current_city]:
                    valid = False
                    break
                current_city = city
            
            # Check constraints
            if city in constraints:
                constraint_met = False
                for (start, end) in constraints[city]:
                    stay_start = day
                    stay_end = day + remaining_days[city] - 1
                    if (stay_start <= end and stay_end >= start):
                        constraint_met = True
                        break
                if not constraint_met:
                    valid = False
                    break
            
            # Allocate days
            days_to_spend = remaining_days[city]
            itinerary.append({
                'day_range': f'Day {day}-{day + days_to_spend - 1}',
                'place': city
            })
            day += days_to_spend
            remaining_days[city] = 0
            
            if day > 16:
                valid = False
                break
        
        if valid and day == 16 and all(days == 0 for days in remaining_days.values()):
            return {"itinerary": itinerary}
    
    return {"itinerary": []}

result = find_itinerary()
print(json.dumps(result, indent=2))