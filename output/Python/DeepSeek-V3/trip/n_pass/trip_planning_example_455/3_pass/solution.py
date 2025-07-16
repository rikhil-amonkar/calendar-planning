import json
from itertools import permutations

def calculate_itinerary():
    # Cities and their required days
    city_days = {
        "Reykjavik": 7,
        "Riga": 2,
        "Warsaw": 3,
        "Istanbul": 6,
        "Krakow": 7
    }
    
    # Direct flight connections
    connections = {
        "Istanbul": ["Krakow", "Warsaw", "Riga"],
        "Krakow": ["Istanbul", "Warsaw"],
        "Warsaw": ["Reykjavik", "Istanbul", "Krakow", "Riga"],
        "Riga": ["Istanbul", "Warsaw"],
        "Reykjavik": ["Warsaw"]
    }
    
    # Constraints - must be entirely within these day ranges
    constraints = {
        "Riga": {"meet_friend": (1, 2)},  # Entire stay must be between day 1-2
        "Istanbul": {"wedding": (2, 7)}    # Entire stay must be between day 2-7
    }
    
    # Total days
    total_days = 21
    
    # Generate all possible permutations of the cities
    cities = list(city_days.keys())
    possible_orders = permutations(cities)
    
    valid_itineraries = []
    
    for order in possible_orders:
        # Check if all consecutive cities in the order are connected
        valid_order = True
        for i in range(len(order) - 1):
            if order[i+1] not in connections[order[i]]:
                valid_order = False
                break
        if not valid_order:
            continue
        
        # Try to assign days to this order
        itinerary = []
        remaining_days = total_days
        current_day = 1
        
        for city in order:
            days_needed = city_days[city]
            if days_needed > remaining_days:
                valid_order = False
                break
            
            end_day = current_day + days_needed - 1
            itinerary.append({
                "day_range": (current_day, end_day),
                "place": city
            })
            current_day = end_day + 1
            remaining_days -= days_needed
        
        if not valid_order:
            continue
        
        # Check constraints - entire stay must be within specified ranges
        meets_constraints = True
        for entry in itinerary:
            city = entry["place"]
            if city in constraints:
                start, end = entry["day_range"]
                min_day, max_day = next(iter(constraints[city].values()))
                # Entire stay must be within the constraint range
                if not (start >= min_day and end <= max_day):
                    meets_constraints = False
                    break
        
        if meets_constraints:
            # Convert day ranges to strings for final output
            formatted_itinerary = []
            for entry in itinerary:
                start, end = entry["day_range"]
                formatted_itinerary.append({
                    "day_range": f"Day {start}-{end}",
                    "place": entry["place"]
                })
            valid_itineraries.append(formatted_itinerary)
    
    if not valid_itineraries:
        return {"error": "No valid itinerary found"}
    
    # Return the first valid itinerary
    return {"itinerary": valid_itineraries[0]}

# Execute and print the result
result = calculate_itinerary()
print(json.dumps(result))