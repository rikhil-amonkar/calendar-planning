import json
from itertools import permutations

def find_itinerary():
    # Define cities and their required days
    cities = {
        'Vienna': {'total_days': 4, 'constraints': [{'day_range': (1, 1), 'required': True}, {'day_range': (4, 4), 'required': True}]},
        'Milan': {'total_days': 2},
        'Rome': {'total_days': 3},
        'Riga': {'total_days': 2},
        'Lisbon': {'total_days': 3, 'constraints': [{'day_range': (11, 13), 'required': True}]},
        'Vilnius': {'total_days': 4},
        'Oslo': {'total_days': 3, 'constraints': [{'day_range': (13, 15), 'required': True}]}
    
    # Define direct flight connections
    connections = {
        'Riga': ['Oslo', 'Rome', 'Vienna', 'Milan', 'Lisbon', 'Vilnius'],
        'Oslo': ['Riga', 'Rome', 'Lisbon', 'Milan', 'Vienna', 'Vilnius'],
        'Rome': ['Oslo', 'Riga', 'Vienna', 'Lisbon'],
        'Vienna': ['Milan', 'Vilnius', 'Lisbon', 'Riga', 'Rome', 'Oslo'],
        'Milan': ['Vienna', 'Riga', 'Oslo', 'Lisbon', 'Vilnius'],
        'Lisbon': ['Vienna', 'Riga', 'Rome', 'Oslo', 'Milan'],
        'Vilnius': ['Vienna', 'Riga', 'Oslo', 'Milan']
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
                    'day': day,
                    'from': current_city,
                    'to': city
                })
                day += 1
                remaining_days[current_city] -= 1
                remaining_days[city] -= 1
                current_city = city
            
            # Add stay days
            stay_days = remaining_days[city]
            if stay_days > 0:
                itinerary.append({
                    'day_range': (day, day + stay_days - 1),
                    'place': city
                })
                day += stay_days
                remaining_days[city] = 0
        
        # Check total days (must be exactly 15)
        if day - 1 != 15:
            continue
            
        # Check all constraints
        # Vienna must be on day 1 and 4
        vienna_days = []
        for entry in itinerary:
            if 'place' in entry and entry['place'] == 'Vienna':
                vienna_days.extend(range(entry['day_range'][0], entry['day_range'][1] + 1))
            elif 'from' in entry and entry['from'] == 'Vienna':
                vienna_days.append(entry['day'])
            elif 'to' in entry and entry['to'] == 'Vienna':
                vienna_days.append(entry['day'])
        if 1 not in vienna_days or 4 not in vienna_days:
            continue
            
        # Lisbon must be between days 11-13
        lisbon_days = []
        for entry in itinerary:
            if 'place' in entry and entry['place'] == 'Lisbon':
                lisbon_days.extend(range(entry['day_range'][0], entry['day_range'][1] + 1))
            elif 'from' in entry and entry['from'] == 'Lisbon':
                lisbon_days.append(entry['day'])
            elif 'to' in entry and entry['to'] == 'Lisbon':
                lisbon_days.append(entry['day'])
        if not any(day in lisbon_days for day in range(11, 14)):
            continue
            
        # Oslo must be between days 13-15
        oslo_days = []
        for entry in itinerary:
            if 'place' in entry and entry['place'] == 'Oslo':
                oslo_days.extend(range(entry['day_range'][0], entry['day_range'][1] + 1))
            elif 'from' in entry and entry['from'] == 'Oslo':
                oslo_days.append(entry['day'])
            elif 'to' in entry and entry['to'] == 'Oslo':
                oslo_days.append(entry['day'])
        if not any(day in oslo_days for day in range(13, 16)):
            continue
            
        # If we get here, we have a valid itinerary
        # Format the output
        formatted_itinerary = []
        for entry in itinerary:
            if 'day_range' in entry:
                formatted_itinerary.append({
                    'day_range': f"Day {entry['day_range'][0]}-{entry['day_range'][1]}",
                    'place': entry['place']
                })
            else:
                formatted_itinerary.append({
                    'day': f"Day {entry['day']}",
                    'action': f"Travel from {entry['from']} to {entry['to']}"
                })
        return {'itinerary': formatted_itinerary}
    
    # If no valid itinerary found
    return {'itinerary': []}

# Execute and print the result
result = find_itinerary()
print(json.dumps(result, indent=2))