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
    
    # Constraints
    constraints = {
        "Oslo": {"day_range": (16, 18)},  # Must be days 16-18
        "Dubrovnik": {"day_range": (5, 9)}  # Must be days 5-9
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
        
        # Assign constrained cities first
        itinerary = []
        valid = True
        
        # Assign Oslo (must be days 16-18)
        oslo_days = cities["Oslo"]
        if "Oslo" in order:
            start_day = 16
            end_day = 18
            if end_day - start_day + 1 < oslo_days:
                valid = False
            else:
                # Mark these days as occupied
                for day in range(start_day, start_day + oslo_days):
                    if day > end_day:
                        valid = False
                        break
                    days[day] = False
                if valid:
                    itinerary.append({
                        "day_range": f"Day {start_day}-{start_day + oslo_days - 1}",
                        "place": "Oslo"
                    })
        
        # Assign Dubrovnik (must be days 5-9)
        dubrovnik_days = cities["Dubrovnik"]
        if "Dubrovnik" in order and valid:
            start_day = 5
            end_day = 9
            if end_day - start_day + 1 < dubrovnik_days:
                valid = False
            else:
                # Find consecutive available days in the range
                found = False
                for s in range(start_day, end_day - dubrovnik_days + 2):
                    if all(days[s + i] for i in range(dubrovnik_days)):
                        # Mark these days as occupied
                        for day in range(s, s + dubrovnik_days):
                            days[day] = False
                        itinerary.append({
                            "day_range": f"Day {s}-{s + dubrovnik_days - 1}",
                            "place": "Dubrovnik"
                        })
                        found = True
                        break
                if not found:
                    valid = False
        
        # Assign remaining cities
        if valid:
            for city in order:
                if city in ["Oslo", "Dubrovnik"]:
                    continue  # already assigned
                
                req_days = cities[city]
                # Find consecutive available days
                found = False
                for start in range(1, total_days - req_days + 2):
                    if all(days[start + i] for i in range(req_days)):
                        # Mark these days as occupied
                        for day in range(start, start + req_days):
                            days[day] = False
                        itinerary.append({
                            "day_range": f"Day {start}-{start + req_days - 1}",
                            "place": city
                        })
                        found = True
                        break
                if not found:
                    valid = False
                    break
        
        # Check if all days are covered
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