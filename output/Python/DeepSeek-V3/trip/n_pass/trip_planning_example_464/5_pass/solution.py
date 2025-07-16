import json
from itertools import permutations

def find_itinerary():
    # Cities and their required days
    cities = {
        "Krakow": 5,
        "Frankfurt": 4,
        "Oslo": 3,
        "Dubrovnik": 5,
        "Naples": 5
    }
    
    # Direct flight connections
    connections = {
        "Dubrovnik": ["Oslo", "Frankfurt", "Naples"],
        "Frankfurt": ["Krakow", "Oslo", "Dubrovnik", "Naples"],
        "Krakow": ["Frankfurt", "Oslo"],
        "Oslo": ["Dubrovnik", "Frankfurt", "Krakow", "Naples"],
        "Naples": ["Oslo", "Dubrovnik", "Frankfurt"]
    }
    
    total_days = 18
    
    # Generate all possible city orders
    city_names = list(cities.keys())
    possible_orders = permutations(city_names)
    
    valid_itineraries = []
    
    for order in possible_orders:
        # Check if all transitions are possible
        valid_transitions = True
        for i in range(len(order) - 1):
            if order[i+1] not in connections[order[i]]:
                valid_transitions = False
                break
        if not valid_transitions:
            continue
        
        # Create a day availability tracker
        days = [True] * (total_days + 1)  # 1-based indexing
        days[0] = False  # Day 0 doesn't exist
        
        itinerary = []
        valid = True
        
        # Assign cities in order
        for city in order:
            req_days = cities[city]
            # Find consecutive available days
            found = False
            for start_day in range(1, total_days - req_days + 2):
                if all(days[start_day + i] for i in range(req_days)):
                    # Mark days as occupied
                    for day in range(start_day, start_day + req_days):
                        days[day] = False
                    itinerary.append({
                        "day_range": f"Day {start_day}-{start_day + req_days - 1}",
                        "place": city
                    })
                    found = True
                    break
            if not found:
                valid = False
                break
        
        # Verify all days are covered exactly
        if valid:
            occupied_days = sum(1 for day in days[1:] if not day)
            if occupied_days == total_days:
                # Sort itinerary by day range
                itinerary.sort(key=lambda x: int(x["day_range"].split('-')[0].split(' ')[1]))
                valid_itineraries.append(itinerary)
    
    if valid_itineraries:
        # Return the first valid itinerary
        return {"itinerary": valid_itineraries[0]}
    else:
        return {"itinerary": []}

# Run the function and print the result
result = find_itinerary()
print(json.dumps(result, indent=2))