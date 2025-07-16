import json
from itertools import permutations

def find_itinerary():
    # Define only the required cities and their days
    cities = {
        'Vienna': {'total_days': 4, 'constraints': [{'day': 1, 'required': True}, {'day': 4, 'required': True}]},
        'Rome': {'total_days': 2},
        'Riga': {'total_days': 1},
        'Oslo': {'total_days': 2, 'constraints': [{'day_range': (13, 15), 'required': True}]},
        'Lisbon': {'total_days': 2, 'constraints': [{'day_range': (11, 13), 'required': True}]}
    
    # Define direct flight connections between only these cities
    connections = {
        'Vienna': ['Rome', 'Riga', 'Oslo', 'Lisbon'],
        'Rome': ['Vienna', 'Riga', 'Oslo', 'Lisbon'],
        'Riga': ['Vienna', 'Rome', 'Oslo', 'Lisbon'],
        'Oslo': ['Vienna', 'Rome', 'Riga', 'Lisbon'],
        'Lisbon': ['Vienna', 'Rome', 'Riga', 'Oslo']
    }

    # Generate all possible city orders (permutations)
    city_names = list(cities.keys())
    possible_orders = permutations(city_names)

    for order in possible_orders:
        # Must start with Vienna (day 1 constraint)
        if order[0] != 'Vienna':
            continue
            
        itinerary = []
        day = 1
        remaining_days = {city: cities[city]['total_days'] for city in city_names}
        current_city = None
        valid = True
        
        for city in order:
            if current_city is None:
                current_city = city
            else:
                # Check flight connection
                if city not in connections[current_city]:
                    valid = False
                    break
                
                # Add travel day
                itinerary.append({
                    'day': f"Day {day}",
                    'action': f"Travel from {current_city} to {city}"
                })
                day += 1
                current_city = city
            
            # Add stay days
            stay_days = cities[city]['total_days']
            start_day = day
            end_day = day + stay_days - 1
            itinerary.append({
                'day_range': f"Day {start_day}-{end_day}",
                'place': city
            })
            day += stay_days
        
        # Check total days (must be exactly 15)
        if day - 1 != 15:
            continue
            
        # Check all constraints
        # Vienna must be on day 1 and 4
        vienna_days = []
        for entry in itinerary:
            if 'place' in entry and entry['place'] == 'Vienna':
                start, end = map(int, entry['day_range'].split(' ')[1].split('-'))
                vienna_days.extend(range(start, end + 1))
            elif 'action' in entry and 'Vienna' in entry['action']:
                vienna_days.append(int(entry['day'].split(' ')[1]))
        
        if 1 not in vienna_days or 4 not in vienna_days:
            continue
            
        # Lisbon must be between days 11-13
        lisbon_days = []
        for entry in itinerary:
            if 'place' in entry and entry['place'] == 'Lisbon':
                start, end = map(int, entry['day_range'].split(' ')[1].split('-'))
                lisbon_days.extend(range(start, end + 1))
            elif 'action' in entry and 'Lisbon' in entry['action']:
                lisbon_days.append(int(entry['day'].split(' ')[1]))
        
        if not any(day in lisbon_days for day in range(11, 14)):
            continue
            
        # Oslo must be between days 13-15
        oslo_days = []
        for entry in itinerary:
            if 'place' in entry and entry['place'] == 'Oslo':
                start, end = map(int, entry['day_range'].split(' ')[1].split('-'))
                oslo_days.extend(range(start, end + 1))
            elif 'action' in entry and 'Oslo' in entry['action']:
                oslo_days.append(int(entry['day'].split(' ')[1]))
        
        if not any(day in oslo_days for day in range(13, 16)):
            continue
            
        # If we get here, we have a valid itinerary
        return {'itinerary': itinerary}
    
    # If no valid itinerary found
    return {'itinerary': []}

# Execute and print the result
result = find_itinerary()
print(json.dumps(result, indent=2))