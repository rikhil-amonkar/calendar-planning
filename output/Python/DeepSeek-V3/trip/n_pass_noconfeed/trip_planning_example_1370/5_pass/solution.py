import json
from itertools import permutations

def find_itinerary():
    cities = {
        'Santorini': {'days': 5, 'constraints': [(25, 29)]},
        'Krakow': {'days': 5, 'constraints': [(18, 22)]},
        'Paris': {'days': 5, 'constraints': [(11, 15)]},
        'Vilnius': {'days': 3, 'constraints': []},
        'Munich': {'days': 5, 'constraints': []},
        'Geneva': {'days': 2, 'constraints': []},
        'Amsterdam': {'days': 4, 'constraints': []},
        'Budapest': {'days': 5, 'constraints': []},
        'Split': {'days': 4, 'constraints': []}
    }
    
    direct_flights = {
        'Paris': ['Krakow', 'Amsterdam', 'Split', 'Geneva', 'Budapest', 'Vilnius', 'Munich'],
        'Krakow': ['Paris', 'Split', 'Munich', 'Amsterdam', 'Vilnius'],
        'Vilnius': ['Munich', 'Split', 'Amsterdam', 'Paris', 'Krakow'],
        'Munich': ['Vilnius', 'Split', 'Amsterdam', 'Geneva', 'Krakow', 'Paris', 'Budapest'],
        'Geneva': ['Paris', 'Amsterdam', 'Split', 'Munich', 'Budapest', 'Santorini'],
        'Amsterdam': ['Paris', 'Geneva', 'Munich', 'Budapest', 'Split', 'Vilnius', 'Krakow', 'Santorini'],
        'Budapest': ['Amsterdam', 'Paris', 'Geneva', 'Munich'],
        'Split': ['Paris', 'Munich', 'Geneva', 'Amsterdam', 'Krakow', 'Vilnius'],
        'Santorini': ['Geneva', 'Amsterdam']
    }
    
    # We'll build the itinerary by first placing the constrained cities in their required slots
    # Then fill in the unconstrained cities around them
    
    # First, place the constrained cities in their required date ranges
    constrained_slots = {
        'Paris': {'start': 11, 'end': 15},
        'Krakow': {'start': 18, 'end': 22},
        'Santorini': {'start': 25, 'end': 29}
    }
    
    # Try different starting points
    for start_city in ['Paris', 'Geneva', 'Amsterdam']:
        # Try different orders for the unconstrained cities
        unconstrained = [c for c in cities if c not in constrained_slots]
        for perm in permutations(unconstrained, len(unconstrained)):
            # Build a potential itinerary order
            itinerary_order = []
            
            # Add cities before Paris (Days 1-10)
            pre_paris = []
            for city in perm:
                if city not in constrained_slots and city not in pre_paris:
                    pre_paris.append(city)
                    if len(pre_paris) >= 3:  # Don't make this section too long
                        break
            
            # Add Paris (Days 11-15)
            itinerary_order.extend(pre_paris)
            itinerary_order.append('Paris')
            
            # Add cities between Paris and Krakow (Days 16-17)
            mid_1 = []
            for city in perm:
                if city not in constrained_slots and city not in pre_paris and city not in mid_1:
                    mid_1.append(city)
                    if len(mid_1) >= 1:  # Only need to fill 2 days here
                        break
            
            # Add Krakow (Days 18-22)
            itinerary_order.extend(mid_1)
            itinerary_order.append('Krakow')
            
            # Add cities between Krakow and Santorini (Days 23-24)
            mid_2 = []
            for city in perm:
                if city not in constrained_slots and city not in pre_paris and city not in mid_1 and city not in mid_2:
                    mid_2.append(city)
                    if len(mid_2) >= 1:  # Only need to fill 2 days here
                        break
            
            # Add Santorini (Days 25-29)
            itinerary_order.extend(mid_2)
            itinerary_order.append('Santorini')
            
            # Add remaining cities after Santorini (Day 30)
            remaining = [c for c in perm if c not in itinerary_order]
            itinerary_order.extend(remaining)
            
            # Verify flight connections
            valid_flights = True
            for i in range(len(itinerary_order)-1):
                if itinerary_order[i+1] not in direct_flights[itinerary_order[i]]:
                    valid_flights = False
                    break
            
            if not valid_flights:
                continue
            
            # Now schedule the itinerary with proper days
            current_day = 1
            itinerary = []
            valid_schedule = True
            
            for city in itinerary_order:
                days_needed = cities[city]['days']
                
                if city in constrained_slots:
                    # Must be in the constrained window
                    constraint = constrained_slots[city]
                    if current_day > constraint['start']:
                        valid_schedule = False
                        break
                    # Move to the start of the constraint window if needed
                    current_day = constraint['start']
                
                end_day = current_day + days_needed - 1
                if end_day > 30:
                    valid_schedule = False
                    break
                
                itinerary.append({
                    'day_range': f"Day {current_day}-{end_day}",
                    'place': city
                })
                current_day = end_day + 1
            
            if valid_schedule and len(itinerary) == len(cities):
                return {'itinerary': itinerary}
    
    return {'itinerary': []}

result = find_itinerary()
print(json.dumps(result, indent=2))