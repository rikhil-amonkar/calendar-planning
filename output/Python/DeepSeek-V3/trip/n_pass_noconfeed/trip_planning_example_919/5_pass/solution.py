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
        'Oslo': [(13, 15)]           # Must be between days 13-15
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
    
    city_list = list(cities.keys())
    total_days = sum(cities.values())
    
    # We'll try starting with Vienna on day 1 or 4 first since it has strict constraints
    for vienna_start in [1, 4]:
        # Create a day allocation template
        days_allocated = [None] * 16  # 1-based indexing, ignore index 0
        
        # Place Vienna first
        vienna_days = cities['Vienna']
        for d in range(vienna_start, vienna_start + vienna_days):
            if d > 15:
                break  # Invalid placement
            days_allocated[d] = 'Vienna'
        else:
            # Now try to place other cities
            remaining_cities = [c for c in city_list if c != 'Vienna']
            
            # Try permutations of remaining cities
            for order in permutations(remaining_cities, len(remaining_cities)):
                temp_days = days_allocated.copy()
                current_city = 'Vienna'
                valid = True
                
                for city in order:
                    # Find the first available block of days for this city
                    city_days = cities[city]
                    placed = False
                    
                    # Try to find a continuous block of days
                    for start_day in range(1, 16 - city_days + 2):
                        end_day = start_day + city_days - 1
                        if end_day > 15:
                            continue
                            
                        # Check if all days in this block are free
                        block_free = True
                        for d in range(start_day, end_day + 1):
                            if temp_days[d] is not None:
                                block_free = False
                                break
                        
                        if block_free:
                            # Check flight connection from previous city
                            prev_city = None
                            for d in range(start_day - 1, 0, -1):
                                if temp_days[d] is not None:
                                    prev_city = temp_days[d]
                                    break
                            
                            if prev_city is None:
                                prev_city = current_city
                            
                            if city not in flight_routes[prev_city]:
                                continue  # No flight route
                            
                            # Check constraints if any
                            if city in constraints:
                                constraint_ok = False
                                for (cons_start, cons_end) in constraints[city]:
                                    # Check if the stay overlaps with constraint period
                                    if not (end_day < cons_start or start_day > cons_end):
                                        constraint_ok = True
                                        break
                                if not constraint_ok:
                                    continue
                            
                            # Place the city
                            for d in range(start_day, end_day + 1):
                                temp_days[d] = city
                            placed = True
                            break
                    
                    if not placed:
                        valid = False
                        break
                
                if valid:
                    # Check if all days are filled
                    if all(d is not None for d in temp_days[1:16]):
                        # Build the itinerary
                        itinerary = []
                        current_place = temp_days[1]
                        start_day = 1
                        
                        for d in range(2, 16):
                            if temp_days[d] != current_place:
                                itinerary.append({
                                    'day_range': f'Day {start_day}-{d-1}',
                                    'place': current_place
                                })
                                current_place = temp_days[d]
                                start_day = d
                        
                        # Add the last segment
                        itinerary.append({
                            'day_range': f'Day {start_day}-15',
                            'place': current_place
                        })
                        
                        return {"itinerary": itinerary}
    
    # If no solution found with Vienna first, try other approaches
    # (Similar logic for other starting cities could be added here)
    
    return {"itinerary": []}

result = find_itinerary()
print(json.dumps(result, indent=2))