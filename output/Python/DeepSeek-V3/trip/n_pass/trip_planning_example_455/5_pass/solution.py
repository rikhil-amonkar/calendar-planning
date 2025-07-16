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
    
    # Constraints - must be exactly these day ranges
    constraints = {
        "Riga": (1, 2),    # Must be exactly days 1-2
        "Istanbul": (2, 7)   # Must be exactly days 2-7
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
        
        # Initialize itinerary
        itinerary = []
        current_day = 1
        days_used = 0
        
        # First handle constrained cities
        constrained_cities = [city for city in order if city in constraints]
        for city in constrained_cities:
            # Riga must be exactly days 1-2
            if city == "Riga":
                itinerary.append({
                    "day_range": (1, 2),
                    "place": "Riga"
                })
                days_used += 2
            
            # Istanbul must be exactly days 2-7
            elif city == "Istanbul":
                itinerary.append({
                    "day_range": (2, 7),
                    "place": "Istanbul"
                })
                days_used += 6
        
        # Now handle unconstrained cities
        for city in order:
            if city in constraints:  # Already handled
                continue
            
            days_needed = city_days[city]
            if days_used + days_needed > total_days:
                valid_order = False
                break
            
            start_day = days_used + 1
            end_day = days_used + days_needed
            itinerary.append({
                "day_range": (start_day, end_day),
                "place": city
            })
            days_used += days_needed
        
        if not valid_order:
            continue
        
        # Verify all cities are included and days equal exactly 21
        included_cities = {entry["place"] for entry in itinerary}
        if included_cities != set(cities):
            continue
        
        if days_used != total_days:
            continue
        
        # Verify flight connections between consecutive cities in itinerary
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