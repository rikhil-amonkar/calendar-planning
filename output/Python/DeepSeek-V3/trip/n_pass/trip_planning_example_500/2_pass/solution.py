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
        
        # First, handle the fixed constraints
        # We know Manchester must include days 19-20 (2 days)
        # We know Lyon must include days 13-14 (2 days)
        
        # We'll try to place these fixed segments first
        for city in order:
            if city == 'Manchester':
                # Must be in Manchester on days 19-20
                start_day = 19
                end_day = 20
                if current_day > start_day:
                    return None  # Can't satisfy constraint
                
                # Add any days before Manchester if needed
                if current_day < start_day:
                    # Try to assign other cities before Manchester
                    for other_city in [c for c in order if c != city]:
                        if remaining_days[other_city] > 0:
                            days_to_assign = min(remaining_days[other_city], start_day - current_day)
                            if days_to_assign > 0:
                                itinerary.append({
                                    'day_range': f"Day {current_day}-{current_day + days_to_assign - 1}",
                                    'place': other_city
                                })
                                remaining_days[other_city] -= days_to_assign
                                current_day += days_to_assign
                                if current_day == start_day:
                                    break
                
                if current_day != start_day or remaining_days[city] < 2:
                    return None
                
                # Assign Manchester days
                itinerary.append({
                    'day_range': f"Day {start_day}-{end_day}",
                    'place': city
                })
                remaining_days[city] -= 2
                current_day = end_day + 1
            
            elif city == 'Lyon':
                # Must be in Lyon on days 13-14
                start_day = 13
                end_day = 14
                if current_day > start_day:
                    return None  # Can't satisfy constraint
                
                # Add any days before Lyon if needed
                if current_day < start_day:
                    # Try to assign other cities before Lyon
                    for other_city in [c for c in order if c != city and c != 'Manchester']:
                        if remaining_days[other_city] > 0:
                            days_to_assign = min(remaining_days[other_city], start_day - current_day)
                            if days_to_assign > 0:
                                itinerary.append({
                                    'day_range': f"Day {current_day}-{current_day + days_to_assign - 1}",
                                    'place': other_city
                                })
                                remaining_days[other_city] -= days_to_assign
                                current_day += days_to_assign
                                if current_day == start_day:
                                    break
                
                if current_day != start_day or remaining_days[city] < 2:
                    return None
                
                # Assign Lyon days
                itinerary.append({
                    'day_range': f"Day {start_day}-{end_day}",
                    'place': city
                })
                remaining_days[city] -= 2
                current_day = end_day + 1
        
        # Now assign remaining days to other cities
        for city in order:
            if remaining_days[city] > 0 and city not in ['Manchester', 'Lyon']:
                # Assign remaining days to this city
                itinerary.append({
                    'day_range': f"Day {current_day}-{current_day + remaining_days[city] - 1}",
                    'place': city
                })
                current_day += remaining_days[city]
                remaining_days[city] = 0
        
        # Verify all constraints are met
        if current_day != total_days + 1 or any(remaining_days.values()):
            return None
        
        # Verify flight connections
        for i in range(len(itinerary) - 1):
            current_city = itinerary[i]['place']
            next_city = itinerary[i+1]['place']
            if not can_fly(current_city, next_city):
                return None
        
        return itinerary
    
    # Try all valid orders to find a working itinerary
    for order in valid_orders:
        itinerary = assign_days(order)
        if itinerary:
            # Sort the itinerary by day range for better presentation
            sorted_itinerary = sorted(itinerary, key=lambda x: int(x['day_range'].split(' ')[1].split('-')[0]))
            return {'itinerary': sorted_itinerary}
    
    return {'itinerary': []}  # Fallback if no solution found

# Execute and print the result
result = find_itinerary()
print(json.dumps(result))