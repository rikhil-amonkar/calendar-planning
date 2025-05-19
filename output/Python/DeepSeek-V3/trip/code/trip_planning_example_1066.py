import json
from itertools import permutations

def main():
    # Input parameters
    total_days = 21
    city_days = {
        'Brussels': 4,
        'Bucharest': 3,
        'Stuttgart': 4,
        'Mykonos': 2,
        'Madrid': 2,
        'Helsinki': 5,
        'Split': 3,
        'London': 5
    }
    
    # Special constraints
    stuttgart_friend_range = (1, 4)  # Stuttgart visit must include day 1-4
    madrid_conference_range = (20, 21)  # Must be in Madrid on days 20-21
    
    # Direct flights
    direct_flights = {
        'Helsinki': ['London', 'Madrid', 'Brussels', 'Split'],
        'London': ['Helsinki', 'Madrid', 'Brussels', 'Bucharest', 'Mykonos', 'Stuttgart', 'Split'],
        'Madrid': ['Helsinki', 'London', 'Bucharest', 'Mykonos', 'Brussels', 'Split'],
        'Brussels': ['London', 'Bucharest', 'Madrid', 'Helsinki'],
        'Bucharest': ['London', 'Brussels', 'Madrid'],
        'Mykonos': ['Madrid', 'London'],
        'Stuttgart': ['London', 'Split'],
        'Split': ['Madrid', 'Helsinki', 'London', 'Stuttgart']
    }
    
    # Generate all possible city orders
    cities = list(city_days.keys())
    possible_orders = permutations(cities)
    
    valid_itineraries = []
    
    for order in possible_orders:
        itinerary = []
        current_day = 1
        valid = True
        
        # Check if Madrid is last (due to conference)
        if order[-1] != 'Madrid':
            continue
        
        # Check if Stuttgart is early enough for friend visit
        stuttgart_pos = order.index('Stuttgart')
        if stuttgart_pos != 0:  # Must be first city to cover days 1-4
            continue
        
        # Build itinerary
        prev_city = None
        for city in order:
            # Check flight connection if not first city
            if prev_city is not None:
                if city not in direct_flights[prev_city]:
                    valid = False
                    break
                # Add flight day
                itinerary.append({
                    'flying': f'Day {current_day}-{current_day}',
                    'from': prev_city,
                    'to': city
                })
                current_day += 0  # Assuming flight doesn't take a full day
            
            # Add city stay
            days = city_days[city]
            end_day = current_day + days - 1
            itinerary.append({
                'day_range': f'Day {current_day}-{end_day}',
                'place': city
            })
            
            # Check special constraints
            if city == 'Stuttgart':
                if not (current_day <= stuttgart_friend_range[0] and end_day >= stuttgart_friend_range[1]):
                    valid = False
                    break
            elif city == 'Madrid':
                if not (current_day <= madrid_conference_range[0] and end_day >= madrid_conference_range[1]):
                    valid = False
                    break
            
            current_day = end_day + 1
            prev_city = city
        
        if valid and current_day - 1 == total_days:
            valid_itineraries.append(itinerary)
    
    # Select first valid itinerary (all should be equivalent given constraints)
    if valid_itineraries:
        output = valid_itineraries[0]
    else:
        output = []
    
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()