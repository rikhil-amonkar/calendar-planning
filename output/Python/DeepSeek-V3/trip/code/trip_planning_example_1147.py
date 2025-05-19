import json
from itertools import permutations

def find_itinerary():
    # Cities and their required days
    cities = {
        'Brussels': 3,
        'Helsinki': 3,
        'Split': 4,
        'Dubrovnik': 2,
        'Istanbul': 5,
        'Milan': 4,
        'Vilnius': 5,
        'Frankfurt': 3
    }
    
    # Fixed events
    fixed_events = [
        {'place': 'Istanbul', 'day_range': (1, 5)},
        {'place': 'Frankfurt', 'day_range': (16, 18)},
        {'place': 'Vilnius', 'day_range': (18, 22)}
    ]
    
    # Direct flights
    direct_flights = {
        'Milan': ['Frankfurt', 'Split', 'Vilnius', 'Brussels', 'Helsinki', 'Istanbul'],
        'Frankfurt': ['Milan', 'Split', 'Helsinki', 'Brussels', 'Dubrovnik', 'Vilnius', 'Istanbul'],
        'Split': ['Frankfurt', 'Milan', 'Helsinki', 'Vilnius'],
        'Brussels': ['Vilnius', 'Helsinki', 'Istanbul', 'Milan', 'Frankfurt'],
        'Helsinki': ['Brussels', 'Istanbul', 'Vilnius', 'Dubrovnik', 'Frankfurt', 'Split', 'Milan'],
        'Istanbul': ['Brussels', 'Helsinki', 'Dubrovnik', 'Milan', 'Frankfurt', 'Vilnius'],
        'Dubrovnik': ['Helsinki', 'Istanbul', 'Frankfurt'],
        'Vilnius': ['Brussels', 'Milan', 'Helsinki', 'Split', 'Frankfurt', 'Istanbul']
    }
    
    # Remaining cities to visit (excluding fixed events)
    remaining_cities = ['Brussels', 'Helsinki', 'Split', 'Dubrovnik', 'Milan']
    remaining_days = cities.copy()
    for event in fixed_events:
        if event['place'] in remaining_days:
            del remaining_days[event['place']]
    
    # Generate possible orders of remaining cities
    possible_orders = permutations(remaining_cities)
    
    # Check each possible order for validity
    valid_itineraries = []
    for order in possible_orders:
        itinerary = []
        current_day = 6  # starts after Istanbul (Day 1-5)
        prev_city = 'Istanbul'
        valid = True
        
        # Add fixed Istanbul stay
        itinerary.append({'day_range': 'Day 1-5', 'place': 'Istanbul'})
        
        for city in order:
            # Check if flight exists
            if city not in direct_flights[prev_city]:
                valid = False
                break
            
            # Add flight
            itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': prev_city, 'to': city})
            
            # Add stay
            stay_days = remaining_days[city]
            end_day = current_day + stay_days - 1
            if end_day > 15:  # must be before Frankfurt (Day 16-18)
                valid = False
                break
            itinerary.append({'day_range': f'Day {current_day}-{end_day}', 'place': city})
            
            prev_city = city
            current_day = end_day + 1
        
        if not valid:
            continue
        
        # Check if we can reach Frankfurt from last city
        if 'Frankfurt' not in direct_flights[prev_city]:
            continue
        
        # Add flight to Frankfurt
        if current_day > 16:
            continue  # must be in Frankfurt by Day 16
        if current_day < 16:
            # Add buffer days if needed
            buffer_days = 16 - current_day
            if buffer_days > 0:
                # Need to stay somewhere before Frankfurt
                # Find a city connected to both prev_city and Frankfurt
                possible_buffer = None
                for buffer_city in direct_flights[prev_city]:
                    if buffer_city in direct_flights and 'Frankfurt' in direct_flights[buffer_city]:
                        possible_buffer = buffer_city
                        break
                if not possible_buffer:
                    continue
                
                # Add flight to buffer city
                itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': prev_city, 'to': possible_buffer})
                current_day += 1
                # Add stay in buffer city (just 1 day)
                itinerary.append({'day_range': f'Day {current_day}-{current_day}', 'place': possible_buffer})
                current_day += 1
                prev_city = possible_buffer
        
        # Add flight to Frankfurt
        itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': prev_city, 'to': 'Frankfurt'})
        
        # Add Frankfurt stay
        itinerary.append({'day_range': 'Day 16-18', 'place': 'Frankfurt'})
        
        # Add flight to Vilnius
        itinerary.append({'flying': 'Day 18-18', 'from': 'Frankfurt', 'to': 'Vilnius'})
        
        # Add Vilnius stay
        itinerary.append({'day_range': 'Day 18-22', 'place': 'Vilnius'})
        
        # Check if all cities are visited
        visited = set()
        for item in itinerary:
            if 'place' in item:
                visited.add(item['place'])
        if len(visited) == 8:
            valid_itineraries.append(itinerary)
    
    if valid_itineraries:
        return valid_itineraries[0]
    else:
        return []

itinerary = find_itinerary()
print(json.dumps(itinerary, indent=2))