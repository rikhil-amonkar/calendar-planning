import json
from itertools import permutations

def calculate_itinerary():
    # Cities and their required days
    cities = {
        "Valencia": 6,
        "Athens": 6,
        "Naples": 5,
        "Zurich": 6
    }
    
    # Direct flights as adjacency list
    flights = {
        "Valencia": ["Naples", "Athens", "Zurich"],
        "Athens": ["Valencia", "Naples", "Zurich"],
        "Naples": ["Valencia", "Athens", "Zurich"],
        "Zurich": ["Naples", "Athens", "Valencia"]
    }
    
    # Constraints
    athens_constraint = (1, 6)  # Must be in Athens between day 1 and 6
    naples_wedding = (16, 20)   # Must be in Naples between day 16 and 20
    
    total_days = 20
    
    # Try different starting cities
    for start_city in cities.keys():
        # Try different orders for visiting cities
        for visit_order in permutations([c for c in cities.keys() if c != start_city]):
            itinerary = []
            remaining_days = {city: cities[city] for city in cities}
            current_city = start_city
            day = 1
            
            # First ensure Athens constraint is met
            if current_city != "Athens":
                # Need to get to Athens by day 6
                days_before_athens = min(5, athens_constraint[1] - 1)  # Max 5 days before Athens
                athens_start = max(athens_constraint[0], day + 1)
                
                # Try to allocate days to starting city before moving to Athens
                days_in_start = min(days_before_athens, remaining_days[current_city])
                if days_in_start > 0:
                    itinerary.append({"day_range": [day, day + days_in_start - 1], "place": current_city})
                    remaining_days[current_city] -= days_in_start
                    day += days_in_start
                
                # Move to Athens
                if "Athens" in flights[current_city]:
                    current_city = "Athens"
                    days_in_athens = min(athens_constraint[1] - day + 1, remaining_days["Athens"], 6)
                    itinerary.append({"day_range": [day, day + days_in_athens - 1], "place": "Athens"})
                    remaining_days["Athens"] -= days_in_athens
                    day += days_in_athens
                else:
                    continue  # Can't reach Athens from starting city
            
            # Now ensure Naples wedding constraint
            if current_city != "Naples":
                # Need to get to Naples by day 20, staying there for wedding days
                # Calculate latest day we can arrive in Naples (wedding is days 16-20)
                latest_arrival = naples_wedding[0]
                
                # Try to allocate remaining days to current city before moving to Naples
                if remaining_days[current_city] > 0:
                    max_days = min(remaining_days[current_city], latest_arrival - day)
                    if max_days > 0:
                        itinerary.append({"day_range": [day, day + max_days - 1], "place": current_city})
                        remaining_days[current_city] -= max_days
                        day += max_days
                
                # Move to Naples
                if "Naples" in flights[current_city]:
                    current_city = "Naples"
                    days_in_naples = min(naples_wedding[1] - day + 1, remaining_days["Naples"], 5)
                    itinerary.append({"day_range": [day, day + days_in_naples - 1], "place": "Naples"})
                    remaining_days["Naples"] -= days_in_naples
                    day += days_in_naples
                else:
                    continue  # Can't reach Naples from current city
            
            # Fill remaining days with other cities
            while day <= total_days and any(v > 0 for v in remaining_days.values()):
                next_city = None
                for city in visit_order:
                    if remaining_days[city] > 0 and city in flights[current_city]:
                        next_city = city
                        break
                
                if next_city is None:
                    break  # No valid next city
                
                # Move to next city
                current_city = next_city
                days_to_spend = min(remaining_days[current_city], total_days - day + 1)
                itinerary.append({"day_range": [day, day + days_to_spend - 1], "place": current_city})
                remaining_days[current_city] -= days_to_spend
                day += days_to_spend
            
            # Check if all constraints are met and all days are allocated
            if day > total_days and all(v == 0 for v in remaining_days.values()):
                # Verify Athens constraint
                athens_ok = False
                for entry in itinerary:
                    if entry["place"] == "Athens":
                        start, end = entry["day_range"]
                        if start <= athens_constraint[1] and end >= athens_constraint[0]:
                            athens_ok = True
                            break
                
                # Verify Naples constraint
                naples_ok = False
                for entry in itinerary:
                    if entry["place"] == "Naples":
                        start, end = entry["day_range"]
                        if start <= naples_wedding[1] and end >= naples_wedding[0]:
                            naples_ok = True
                            break
                
                if athens_ok and naples_ok:
                    # Format the itinerary
                    formatted_itinerary = []
                    for entry in itinerary:
                        start, end = entry["day_range"]
                        if start == end:
                            day_range = f"Day {start}"
                        else:
                            day_range = f"Day {start}-{end}"
                        formatted_itinerary.append({
                            "day_range": day_range,
                            "place": entry["place"]
                        })
                    return {"itinerary": formatted_itinerary}
    
    return {"itinerary": []}

result = calculate_itinerary()
print(json.dumps(result, indent=2))