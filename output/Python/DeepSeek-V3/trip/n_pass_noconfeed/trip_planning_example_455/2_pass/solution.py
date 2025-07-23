import json
from itertools import permutations

def calculate_itinerary():
    cities = {
        'Reykjavik': 7,
        'Riga': 2,
        'Warsaw': 3,
        'Istanbul': 6,
        'Krakow': 7
    }
    
    flight_connections = {
        'Istanbul': ['Krakow', 'Warsaw', 'Riga'],
        'Krakow': ['Istanbul', 'Warsaw'],
        'Warsaw': ['Istanbul', 'Krakow', 'Reykjavik', 'Riga'],
        'Riga': ['Istanbul', 'Warsaw'],
        'Reykjavik': ['Warsaw']
    }
    
    total_days = 21
    constraints = {
        'Riga': (1, 2),    # Must be in Riga between day 1-2
        'Istanbul': (2, 7)  # Must be in Istanbul between day 2-7
    }
    
    # Generate all possible city orders that satisfy flight connections
    city_names = list(cities.keys())
    possible_orders = permutations(city_names)
    
    valid_itineraries = []
    
    for order in possible_orders:
        # Check flight connections
        valid_flights = True
        for i in range(len(order)-1):
            if order[i+1] not in flight_connections.get(order[i], []):
                valid_flights = False
                break
        if not valid_flights:
            continue
        
        # Try to assign days
        itinerary = []
        remaining_days = total_days
        remaining_cities = set(city_names)
        day_assignments = {}
        
        # First assign constrained cities
        try:
            # Assign Riga first (must be days 1-2)
            if 'Riga' in order:
                start_day = max(1, constraints['Riga'][0])
                end_day = min(start_day + cities['Riga'] - 1, constraints['Riga'][1])
                if end_day - start_day + 1 < cities['Riga']:
                    continue  # Can't fit Riga visit in required window
                day_assignments['Riga'] = (start_day, end_day)
                remaining_cities.remove('Riga')
            
            # Assign Istanbul next (must be days 2-7)
            if 'Istanbul' in order:
                istanbul_days = cities['Istanbul']
                # Find earliest possible start that fits after Riga if assigned
                earliest_start = 2
                if 'Riga' in day_assignments:
                    earliest_start = max(earliest_start, day_assignments['Riga'][1] + 1)
                start_day = max(earliest_start, constraints['Istanbul'][0])
                end_day = min(start_day + istanbul_days - 1, constraints['Istanbul'][1])
                if end_day - start_day + 1 < istanbul_days:
                    continue  # Can't fit Istanbul visit in required window
                day_assignments['Istanbul'] = (start_day, end_day)
                remaining_cities.remove('Istanbul')
        except:
            continue
        
        # Now assign remaining cities in order, checking flight connections
        current_day = 1
        temp_itinerary = []
        remaining_to_assign = [city for city in order if city in remaining_cities]
        
        for city in remaining_to_assign:
            if city in day_assignments:
                continue
            
            days_needed = cities[city]
            start_day = current_day
            end_day = start_day + days_needed - 1
            
            # Check if this overlaps with any constrained city
            valid = True
            for assigned_city, (assigned_start, assigned_end) in day_assignments.items():
                if not (end_day < assigned_start or start_day > assigned_end):
                    valid = False
                    break
            if not valid:
                continue
            
            day_assignments[city] = (start_day, end_day)
            current_day = end_day + 1
        
        # Check if all cities are assigned and total days is 21
        if len(day_assignments) == len(cities):
            # Create ordered itinerary
            itinerary = []
            for day in range(1, total_days + 1):
                for city, (start, end) in day_assignments.items():
                    if start <= day <= end:
                        itinerary.append({
                            'day': f"Day {day}",
                            'place': city
                        })
                        break
            
            # Verify all constraints are met
            meets_constraints = True
            for city, (constraint_start, constraint_end) in constraints.items():
                city_start, city_end = day_assignments[city]
                if not (city_start <= constraint_end and city_end >= constraint_start):
                    meets_constraints = False
                    break
            
            if meets_constraints:
                # Group consecutive days in the same city
                grouped_itinerary = []
                current_entry = None
                for entry in itinerary:
                    if current_entry and current_entry['place'] == entry['place']:
                        current_entry['day_range'] = current_entry['day_range'].split('-')[0] + '-' + entry['day'].split(' ')[1]
                    else:
                        if current_entry:
                            grouped_itinerary.append(current_entry)
                        current_entry = {
                            'day_range': entry['day'] + '-' + entry['day'].split(' ')[1],
                            'place': entry['place']
                        }
                if current_entry:
                    grouped_itinerary.append(current_entry)
                
                valid_itineraries.append(grouped_itinerary)
    
    if valid_itineraries:
        # Return the first valid itinerary
        return {'itinerary': valid_itineraries[0]}
    else:
        return {'itinerary': []}

result = calculate_itinerary()
print(json.dumps(result, indent=2))