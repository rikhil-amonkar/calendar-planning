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
        
        # First assign the fixed days
        # Lyon must be on days 13-14
        # Manchester must be on days 19-20
        
        # Process days 1-12 (before Lyon)
        days_needed = 12
        days_assigned = 0
        for city in order:
            if city in ['Lyon', 'Manchester']:
                continue  # Save these for their fixed days
            if remaining_days[city] > 0:
                assign = min(remaining_days[city], days_needed - days_assigned)
                if assign > 0:
                    start_day = current_day + days_assigned
                    end_day = start_day + assign - 1
                    itinerary.append({
                        'day_range': f"Day {start_day}-{end_day}",
                        'place': city
                    })
                    remaining_days[city] -= assign
                    days_assigned += assign
                    if days_assigned == days_needed:
                        break
        
        # Check if we successfully assigned days 1-12
        if days_assigned != 12:
            return None
        
        # Assign Lyon days 13-14
        if remaining_days['Lyon'] < 2:
            return None
        itinerary.append({
            'day_range': "Day 13-14",
            'place': 'Lyon'
        })
        remaining_days['Lyon'] -= 2
        
        # Process days 15-18 (between Lyon and Manchester)
        days_needed = 4
        days_assigned = 0
        for city in order:
            if city == 'Manchester':
                continue  # Save for fixed days
            if remaining_days[city] > 0:
                assign = min(remaining_days[city], days_needed - days_assigned)
                if assign > 0:
                    start_day = 15 + days_assigned
                    end_day = start_day + assign - 1
                    itinerary.append({
                        'day_range': f"Day {start_day}-{end_day}",
                        'place': city
                    })
                    remaining_days[city] -= assign
                    days_assigned += assign
                    if days_assigned == days_needed:
                        break
        
        # Check if we successfully assigned days 15-18
        if days_assigned != 4:
            return None
        
        # Assign Manchester days 19-20
        if remaining_days['Manchester'] < 2:
            return None
        itinerary.append({
            'day_range': "Day 19-20",
            'place': 'Manchester'
        })
        remaining_days['Manchester'] -= 2
        
        # Verify all days are assigned and constraints met
        if any(remaining_days.values()):
            return None
        
        # Verify flight connections between segments
        # Sort itinerary by day range
        sorted_itinerary = sorted(itinerary, key=lambda x: int(x['day_range'].split(' ')[1].split('-')[0]))
        
        # Check flights between segments
        for i in range(len(sorted_itinerary) - 1):
            current_city = sorted_itinerary[i]['place']
            next_city = sorted_itinerary[i+1]['place']
            if not can_fly(current_city, next_city):
                return None
        
        return sorted_itinerary
    
    # Try all valid orders to find a working itinerary
    for order in valid_orders:
        itinerary = assign_days(order)
        if itinerary:
            return {'itinerary': itinerary}
    
    return {'itinerary': []}  # Fallback if no solution found

# Execute and print the result
result = find_itinerary()
print(json.dumps(result))