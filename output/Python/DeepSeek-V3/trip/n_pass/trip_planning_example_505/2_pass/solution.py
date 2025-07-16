import json
from itertools import permutations

def find_itinerary():
    # Define the constraints
    total_days = 8
    city_stays = {
        'Prague': 4,
        'Stuttgart': 2,
        'Split': 2,
        'Krakow': 2,
        'Florence': 2
    }
    
    # Define the flight connections
    flight_connections = {
        'Stuttgart': ['Split', 'Krakow'],
        'Prague': ['Florence', 'Split', 'Krakow'],
        'Split': ['Stuttgart', 'Krakow', 'Prague'],
        'Krakow': ['Stuttgart', 'Split', 'Prague'],
        'Florence': ['Prague']
    }
    
    # Wedding in Stuttgart between day 2 and day 3 means Stuttgart must include day 2 or day 3
    # Friends in Split between day 3 and day 4 means Split must include day 3 or day 4
    
    # Generate all possible permutations of the cities
    cities = list(city_stays.keys())
    possible_orders = permutations(cities)
    
    valid_itineraries = []
    
    for order in possible_orders:
        # Check if the order respects flight connections
        valid_order = True
        for i in range(len(order) - 1):
            if order[i+1] not in flight_connections.get(order[i], []):
                valid_order = False
                break
        if not valid_order:
            continue
        
        # Try to assign days to this order
        current_day = 1
        itinerary = []
        city_days = {city: 0 for city in cities}
        
        for city in order:
            required_days = city_stays[city]
            start_day = current_day
            end_day = current_day + required_days - 1
            
            # Check if we exceed total days
            if end_day > total_days:
                valid_order = False
                break
            
            # Check specific city constraints
            if city == 'Stuttgart':
                if not (start_day <= 2 <= end_day or start_day <= 3 <= end_day):
                    valid_order = False
                    break
            
            if city == 'Split':
                if not (start_day <= 3 <= end_day or start_day <= 4 <= end_day):
                    valid_order = False
                    break
            
            # Assign the days
            itinerary.append({
                'day_range': f"Day {start_day}-{end_day}",
                'place': city
            })
            city_days[city] += required_days
            current_day = end_day + 1
        
        # Check if all cities got their required days and exactly 8 days are used
        if (valid_order and 
            all(city_days[city] == city_stays[city] for city in cities) and 
            current_day - 1 == total_days):
            valid_itineraries.append(itinerary)
    
    # Select the first valid itinerary
    if valid_itineraries:
        return {"itinerary": valid_itineraries[0]}
    else:
        return {"itinerary": []}

# Execute the function and print the result
result = find_itinerary()
print(json.dumps(result))