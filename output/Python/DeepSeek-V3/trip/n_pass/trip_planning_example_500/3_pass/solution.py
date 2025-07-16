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
    manchester_days = (19, 20)  # Must be in Manchester on these days
    lyon_days = (13, 14)        # Must be in Lyon on these days
    
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
        
        # First handle the fixed constraints
        # We'll process the itinerary in segments, making sure to be in:
        # - Lyon on days 13-14
        # - Manchester on days 19-20
        
        # Process days 1-12
        days_before_lyon = 12
        days_to_assign = days_before_lyon - current_day + 1
        if days_to_assign > 0:
            for city in order:
                if city in ['Lyon', 'Manchester']:
                    continue  # Save these for their fixed days
                if remaining_days[city] > 0:
                    assign = min(remaining_days[city], days_to_assign)
                    if assign > 0:
                        itinerary.append({
                            'day_range': f"Day {current_day}-{current_day + assign - 1}",
                            'place': city
                        })
                        remaining_days[city] -= assign
                        current_day += assign
                        days_to_assign -= assign
                        if days_to_assign == 0:
                            break
        
        # Process Lyon days 13-14
        if current_day != 13:
            return None  # Couldn't properly assign days before Lyon
        itinerary.append({
            'day_range': "Day 13-14",
            'place': 'Lyon'
        })
        remaining_days['Lyon'] -= 2
        current_day = 15
        
        # Process days 15-18
        days_before_manchester = 18
        days_to_assign = days_before_manchester - current_day + 1
        if days_to_assign > 0:
            for city in order:
                if city == 'Manchester':
                    continue  # Save for fixed days
                if remaining_days[city] > 0:
                    assign = min(remaining_days[city], days_to_assign)
                    if assign > 0:
                        itinerary.append({
                            'day_range': f"Day {current_day}-{current_day + assign - 1}",
                            'place': city
                        })
                        remaining_days[city] -= assign
                        current_day += assign
                        days_to_assign -= assign
                        if days_to_assign == 0:
                            break
        
        # Process Manchester days 19-20
        if current_day != 19:
            return None  # Couldn't properly assign days before Manchester
        itinerary.append({
            'day_range': "Day 19-20",
            'place': 'Manchester'
        })
        remaining_days['Manchester'] -= 2
        current_day = 21
        
        # Verify all days are assigned and constraints met
        if current_day != 21 or any(remaining_days.values()):
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