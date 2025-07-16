import json
from itertools import permutations

def find_itinerary():
    # Define the constraints
    total_days = 20
    city_days = {
        'Hamburg': 7,
        'Munich': 6,
        'Manchester': 2,
        'Lyon': 2,
        'Split': 7
    }
    # Special constraints
    manchester_relatives = (19, 20)  # Must be in Manchester on these days
    lyon_show = (13, 14)             # Must be in Lyon on these days
    
    # Direct flights as adjacency list
    flights = {
        'Split': ['Munich', 'Lyon', 'Hamburg', 'Manchester'],
        'Munich': ['Split', 'Manchester', 'Hamburg', 'Lyon'],
        'Manchester': ['Munich', 'Hamburg', 'Split'],
        'Hamburg': ['Manchester', 'Munich', 'Split'],
        'Lyon': ['Split', 'Munich']
    }
    
    # Correct city names in flights (fixing typos)
    corrected_flights = {
        'Split': ['Munich', 'Lyon', 'Hamburg', 'Manchester'],
        'Munich': ['Split', 'Manchester', 'Hamburg', 'Lyon'],
        'Manchester': ['Munich', 'Hamburg', 'Split'],
        'Hamburg': ['Manchester', 'Munich', 'Split'],
        'Lyon': ['Split', 'Munich']
    }
    flights = corrected_flights
    
    # Generate all possible city orders (permutations)
    cities = list(city_days.keys())
    possible_orders = permutations(cities)
    
    # Function to check if a flight is possible
    def can_fly(from_city, to_city):
        return to_city in flights.get(from_city, [])
    
    # Function to validate an itinerary
    def validate_itinerary(order):
        # Check flight connections
        for i in range(len(order) - 1):
            if not can_fly(order[i], order[i+1]):
                return False
        return True
    
    # Find all valid city orders
    valid_orders = [order for order in possible_orders if validate_itinerary(order)]
    
    # Function to generate day assignments for an order
    def assign_days(order):
        remaining_days = city_days.copy()
        itinerary = []
        current_day = 1
        
        for i, city in enumerate(order):
            # Determine how many days to spend in this city
            days_needed = remaining_days[city]
            
            # Handle special constraints
            if city == 'Manchester':
                # Must be in Manchester on days 19-20
                if current_day <= 19 <= current_day + days_needed - 1:
                    pass  # Already satisfies
                elif 19 >= current_day + days_needed:
                    # Need to adjust to include day 19
                    days_needed = 19 - current_day + 1
                    if days_needed < 2:
                        days_needed = 2
                elif 19 < current_day:
                    # Can't satisfy, skip this order
                    return None
            
            if city == 'Lyon':
                # Must be in Lyon on days 13-14
                if current_day <= 13 <= current_day + days_needed - 1:
                    pass  # Already satisfies
                elif 13 >= current_day + days_needed:
                    # Need to adjust to include day 13
                    days_needed = 13 - current_day + 1
                    if days_needed < 2:
                        days_needed = 2
                elif 13 < current_day:
                    # Can't satisfy, skip this order
                    return None
            
            # Assign days
            end_day = current_day + days_needed - 1
            if end_day > total_days:
                return None  # Exceeds total days
            
            itinerary.append({
                'day_range': f"Day {current_day}-{end_day}",
                'place': city
            })
            
            remaining_days[city] -= days_needed
            current_day = end_day + 1
        
        # Check if all days are assigned and constraints are met
        if current_day <= total_days:
            return None
        
        # Verify all city days are satisfied
        if any(remaining_days.values()):
            return None
        
        # Verify special constraints
        manchester_ok = False
        lyon_ok = False
        for entry in itinerary:
            start, end = map(int, entry['day_range'].split(' ')[1].split('-'))
            place = entry['place']
            if place == 'Manchester':
                if start <= manchester_relatives[0] <= end and start <= manchester_relatives[1] <= end:
                    manchester_ok = True
            if place == 'Lyon':
                if start <= lyon_show[0] <= end and start <= lyon_show[1] <= end:
                    lyon_ok = True
        
        if not manchester_ok or not lyon_ok:
            return None
        
        return itinerary
    
    # Try all valid orders to find a working itinerary
    for order in valid_orders:
        itinerary = assign_days(order)
        if itinerary:
            return {'itinerary': itinerary}
    
    return {'itinerary': []}  # Fallback if no solution found

# Execute and print the result
result = find_itinerary()
print(json.dumps(result))