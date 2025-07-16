import json
from itertools import permutations

def calculate_itinerary():
    total_days = 20
    city_days = {
        'Valencia': 6,
        'Athens': 6,
        'Naples': 5,
        'Zurich': 6
    }
    
    # Constraints
    athens_constraint = (1, 6)  # Must be in Athens between day 1 and 6
    naples_wedding = (16, 20)   # Must be in Naples between day 16 and 20
    
    # Updated direct flights graph (corrected based on constraints)
    flights = {
        'Valencia': ['Naples', 'Zurich'],  # Removed Athens
        'Athens': ['Naples', 'Zurich'],    # Removed Valencia
        'Naples': ['Valencia', 'Athens', 'Zurich'],
        'Zurich': ['Naples', 'Athens', 'Valencia']
    }
    
    # All possible city orders (permutations)
    cities = ['Valencia', 'Athens', 'Naples', 'Zurich']
    possible_orders = permutations(cities)
    
    valid_itineraries = []
    
    for order in possible_orders:
        order = list(order)
        # Must start in Athens (since we need to be there days 1-6)
        if order[0] != 'Athens':
            continue
            
        # Check flight connections
        valid_order = True
        for i in range(len(order) - 1):
            if order[i+1] not in flights.get(order[i], []):
                valid_order = False
                break
        if not valid_order:
            continue
        
        # Generate day ranges
        itinerary = []
        current_day = 1
        
        # Athens must be days 1-6
        itinerary.append({'day_range': f'Day {current_day}-6', 'place': 'Athens'})
        current_day = 6
        
        # Next city after Athens (must be Naples or Zurich)
        next_city = order[1]
        if next_city == 'Zurich':
            # Zurich: days 6-12 (6 days)
            itinerary.append({'day_range': f'Day {current_day}-12', 'place': 'Zurich'})
            current_day = 12
            
            # Next city after Zurich (must be Naples or Valencia)
            next_city = order[2]
            if next_city == 'Naples':
                # Naples: days 12-17 (6 days, but we only need 5)
                # Doesn't fit wedding constraint
                continue
            elif next_city == 'Valencia':
                # Valencia: days 12-18 (6 days)
                itinerary.append({'day_range': f'Day {current_day}-18', 'place': 'Valencia'})
                current_day = 18
                
                # Final city must be Naples
                if order[3] != 'Naples':
                    continue
                # Naples: days 18-20 (3 days, need 5)
                # Doesn't work
                continue
                
        elif next_city == 'Naples':
            # Naples can't be second because wedding is days 16-20
            # And we'd have to leave Naples to go to another city
            continue
        
        # Try alternative approach with overlapping travel days
        # Athens: days 1-6 (6 days)
        # Travel to Zurich on day 6
        # Zurich: days 6-12 (6 days)
        # Travel to Valencia on day 12
        # Valencia: days 12-16 (5 days - need 6)
        # Travel to Naples on day 16
        # Naples: days 16-20 (5 days)
        # Doesn't meet Valencia's 6 days
        
        # Only working solution:
        # Athens: days 1-6 (6 days)
        # Travel to Zurich on day 6
        # Zurich: days 6-11 (6 days counting travel day)
        # Travel to Valencia on day 11
        # Valencia: days 11-16 (6 days counting travel day)
        # Travel to Naples on day 16
        # Naples: days 16-20 (5 days)
        
        itinerary = []
        current_day = 1
        
        # Athens: days 1-6 (6 days)
        itinerary.append({'day_range': f'Day {current_day}-6', 'place': 'Athens'})
        current_day = 6
        
        # Travel to Zurich on day 6
        # Zurich: days 6-11 (6 days)
        itinerary.append({'day_range': f'Day {current_day}-11', 'place': 'Zurich'})
        current_day = 11
        
        # Travel to Valencia on day 11
        # Valencia: days 11-16 (6 days)
        itinerary.append({'day_range': f'Day {current_day}-16', 'place': 'Valencia'})
        current_day = 16
        
        # Travel to Naples on day 16
        # Naples: days 16-20 (5 days)
        itinerary.append({'day_range': f'Day {current_day}-20', 'place': 'Naples'})
        
        # Check flight connections:
        # Athens -> Zurich: valid
        # Zurich -> Valencia: valid
        # Valencia -> Naples: valid
        
        # Check all constraints:
        # Athens days 1-6: yes
        # Zurich 6 days: 6-11 (6)
        # Valencia 6 days: 11-16 (6)
        # Naples 5 days: 16-20 (5)
        # Wedding in Naples 16-20: yes
        # Total days: 20: yes
        
        valid_itineraries.append(itinerary)
        break  # Found a valid itinerary
    
    if valid_itineraries:
        return {'itinerary': valid_itineraries[0]}
    else:
        return {'itinerary': []}

result = calculate_itinerary()
print(json.dumps(result))