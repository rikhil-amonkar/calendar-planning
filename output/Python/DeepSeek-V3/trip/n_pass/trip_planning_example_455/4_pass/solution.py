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
        "Riga": {"meet_friend": (1, 2)},  # Must be exactly days 1-2
        "Istanbul": {"wedding": (2, 7)}    # Must be exactly days 2-7
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
        
        # Try to assign days to this order with constraints
        itinerary = []
        remaining_days = total_days
        current_day = 1
        
        # First handle constrained cities
        constrained_cities = [city for city in order if city in constraints]
        for city in constrained_cities:
            # Riga must be exactly days 1-2
            if city == "Riga":
                if city_days["Riga"] != 2:
                    valid_order = False
                    break
                itinerary.append({
                    "day_range": (1, 2),
                    "place": "Riga"
                })
                current_day = 3  # Next available day
            
            # Istanbul must be exactly days 2-7
            elif city == "Istanbul":
                if city_days["Istanbul"] != 6:
                    valid_order = False
                    break
                itinerary.append({
                    "day_range": (2, 7),
                    "place": "Istanbul"
                })
                current_day = 8  # Next available day
        
        if not valid_order:
            continue
        
        # Now handle unconstrained cities
        for city in order:
            if city in constraints:  # Already handled
                continue
            
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
        
        # Verify all cities are included and days don't exceed total
        included_cities = {entry["place"] for entry in itinerary}
        if included_cities != set(cities):
            continue
        
        if current_day - 1 > total_days:
            continue
        
        # Verify flight connections between consecutive cities in itinerary
        # Sort itinerary by day range
        sorted_itinerary = sorted(itinerary, key=lambda x: x["day_range"][0])
        for i in range(len(sorted_itinerary) - 1):
            current_city = sorted_itinerary[i]["place"]
            next_city = sorted_itinerary[i+1]["place"]
            if next_city not in connections[current_city]:
                valid_order = False
                break
        
        if valid_order:
            # Convert day ranges to strings for final output
            formatted_itinerary = []
            for entry in sorted_itinerary:
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