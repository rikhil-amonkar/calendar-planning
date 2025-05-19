import json
from itertools import permutations

def find_optimal_itinerary():
    # Input parameters
    total_days = 12
    city_days = {
        'Frankfurt': 3,
        'Naples': 4,
        'Helsinki': 4,
        'Lyon': 3,
        'Prague': 2
    }
    
    # Flight connections
    flight_connections = {
        'Prague': ['Lyon', 'Frankfurt', 'Helsinki'],
        'Lyon': ['Prague', 'Frankfurt'],
        'Frankfurt': ['Prague', 'Lyon', 'Helsinki', 'Naples'],
        'Helsinki': ['Prague', 'Frankfurt', 'Naples'],
        'Naples': ['Helsinki', 'Frankfurt']
    }
    
    # Constraints
    helsinki_constraint = (2, 5)  # Helsinki must be visited from day 2 to day 5
    prague_workshop = (1, 2)      # Must be in Prague between day 1 and day 2
    
    # Generate all possible city orders
    cities = list(city_days.keys())
    possible_orders = permutations(cities)
    
    valid_itineraries = []
    
    for order in possible_orders:
        # Check if flight connections are valid
        valid_flights = True
        for i in range(len(order) - 1):
            if order[i+1] not in flight_connections[order[i]]:
                valid_flights = False
                break
        if not valid_flights:
            continue
        
        # Try to schedule the cities in this order
        current_day = 1
        itinerary = []
        prague_visited = False
        helsinki_visited = False
        
        for city in order:
            days = city_days[city]
            
            # Check if we can place the city in the remaining days
            if current_day + days - 1 > total_days:
                break
            
            # Check Prague workshop constraint
            if city == 'Prague':
                if not (prague_workshop[0] <= current_day <= prague_workshop[1] or 
                       prague_workshop[0] <= current_day + days - 1 <= prague_workshop[1]):
                    break
                prague_visited = True
            
            # Check Helsinki show constraint
            if city == 'Helsinki':
                helsinki_start = current_day
                helsinki_end = current_day + days - 1
                if not (helsinki_constraint[0] <= helsinki_start and helsinki_end <= helsinki_constraint[1]):
                    break
                helsinki_visited = True
            
            # Add city stay to itinerary
            itinerary.append({
                'day_range': f'Day {current_day}-{current_day + days - 1}',
                'place': city
            })
            
            current_day += days
            
            # Add flight to next city if not last city
            if city != order[-1]:
                next_city = order[order.index(city)+1]
                itinerary.append({
                    'flying': f'Day {current_day-1}-{current_day-1}',
                    'from': city,
                    'to': next_city
                })
        
        # Check if all days are used and constraints are met
        if (current_day - 1 == total_days and prague_visited and helsinki_visited):
            valid_itineraries.append(itinerary)
    
    # Select the first valid itinerary (all valid ones should be equivalent in days)
    if valid_itineraries:
        return valid_itineraries[0]
    else:
        return []

# Compute and output the itinerary
itinerary = find_optimal_itinerary()
print(json.dumps(itinerary, indent=2))