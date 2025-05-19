import json
from itertools import permutations

def find_itinerary():
    # Input parameters
    total_days = 18
    cities = {
        'Tallinn': {'days': 2, 'constraints': []},
        'Bucharest': {'days': 4, 'constraints': [{'start': 1, 'end': 4}]},
        'Seville': {'days': 5, 'constraints': [{'start': 8, 'end': 12}]},
        'Stockholm': {'days': 5, 'constraints': []},
        'Munich': {'days': 5, 'constraints': [{'start': 4, 'end': 8}]},
        'Milan': {'days': 2, 'constraints': []}
    }
    
    direct_flights = {
        'Milan': ['Stockholm', 'Munich', 'Seville'],
        'Stockholm': ['Milan', 'Munich', 'Tallinn'],
        'Munich': ['Stockholm', 'Bucharest', 'Seville', 'Milan', 'Tallinn'],
        'Bucharest': ['Munich'],
        'Seville': ['Munich', 'Milan'],
        'Tallinn': ['Stockholm', 'Munich']
    }
    
    # Generate all possible permutations of cities
    city_names = list(cities.keys())
    possible_orders = permutations(city_names)
    
    valid_itineraries = []
    
    for order in possible_orders:
        itinerary = []
        current_day = 1
        valid = True
        
        # Check if Bucharest is visited between day 1 and 4
        bucharest_pos = order.index('Bucharest')
        bucharest_start = current_day
        for i in range(bucharest_pos):
            bucharest_start += cities[order[i]]['days']
        bucharest_end = bucharest_start + cities['Bucharest']['days'] - 1
        if not (1 <= bucharest_start <= 4 and 1 <= bucharest_end <= 4):
            valid = False
        
        # Check if Munich is visited between day 4 and 8
        munich_pos = order.index('Munich')
        munich_start = current_day
        for i in range(munich_pos):
            munich_start += cities[order[i]]['days']
        munich_end = munich_start + cities['Munich']['days'] - 1
        if not (4 <= munich_start <= 8 and 4 <= munich_end <= 8):
            valid = False
        
        # Check if Seville is visited between day 8 and 12
        seville_pos = order.index('Seville')
        seville_start = current_day
        for i in range(seville_pos):
            seville_start += cities[order[i]]['days']
        seville_end = seville_start + cities['Seville']['days'] - 1
        if not (8 <= seville_start <= 12 and 8 <= seville_end <= 12):
            valid = False
        
        # Check flight connections
        for i in range(len(order) - 1):
            from_city = order[i]
            to_city = order[i + 1]
            if to_city not in direct_flights[from_city]:
                valid = False
                break
        
        if valid:
            # Build itinerary
            day = 1
            for i, city in enumerate(order):
                days = cities[city]['days']
                itinerary.append({
                    'day_range': f'Day {day}-{day + days - 1}',
                    'place': city
                })
                day += days
                if i < len(order) - 1:
                    itinerary.append({
                        'flying': f'Day {day - 1}-{day - 1}',
                        'from': city,
                        'to': order[i + 1]
                    })
            
            # Check total days
            total_itinerary_days = sum(cities[city]['days'] for city in order)
            if total_itinerary_days == total_days:
                valid_itineraries.append(itinerary)
    
    return valid_itineraries[0] if valid_itineraries else []

itinerary = find_itinerary()
print(json.dumps(itinerary, indent=2))