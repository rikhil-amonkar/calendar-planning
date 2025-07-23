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
    constraints = [
        ('Riga', 1, 2),  # Meet friend in Riga between day 1 and day 2
        ('Istanbul', 2, 7)  # Attend wedding in Istanbul between day 2 and day 7
    ]
    
    # Generate all possible city orders
    city_names = list(cities.keys())
    possible_orders = permutations(city_names)
    
    valid_itineraries = []
    
    for order in possible_orders:
        # Check if all flight connections are valid
        valid_order = True
        for i in range(len(order) - 1):
            from_city = order[i]
            to_city = order[i + 1]
            if to_city not in flight_connections.get(from_city, []):
                valid_order = False
                break
        if not valid_order:
            continue
        
        # Try to assign days
        itinerary = []
        current_day = 1
        remaining_cities = {city: days for city, days in cities.items()}
        
        for city in order:
            days_needed = remaining_cities[city]
            start_day = current_day
            end_day = current_day + days_needed - 1
            
            # Check constraints
            meets_constraints = True
            for const_city, const_start, const_end in constraints:
                if const_city == city:
                    if not (start_day <= const_end and end_day >= const_start):
                        meets_constraints = False
                        break
            
            if not meets_constraints:
                break
            
            itinerary.append({
                'day_range': f"Day {start_day}-{end_day}",
                'place': city
            })
            current_day = end_day + 1
            remaining_cities[city] = 0
        
        # Check if all cities are visited and total days is 21
        if sum(remaining_cities.values()) == 0 and current_day - 1 == total_days:
            valid_itineraries.append(itinerary)
    
    if valid_itineraries:
        # Select the first valid itinerary (can be optimized further)
        best_itinerary = valid_itineraries[0]
        return {'itinerary': best_itinerary}
    else:
        return {'itinerary': []}

result = calculate_itinerary()
print(json.dumps(result, indent=2))