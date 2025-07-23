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
    athens_constraint = (1, 6)  # Must visit Athens at least once between day 1 and 6
    naples_wedding = (16, 20)   # Must be in Naples between day 16 and 20
    
    total_days = 20
    
    # Try different starting cities
    for start_city in cities.keys():
        # Try different orders for visiting remaining cities
        other_cities = [c for c in cities.keys() if c != start_city]
        for visit_order in permutations(other_cities):
            itinerary = []
            remaining_days = {city: cities[city] for city in cities}
            current_city = start_city
            day = 1
            
            # First, handle Athens constraint (must visit between day 1-6)
            if current_city != "Athens":
                # Calculate how many days we can spend in starting city before needing to go to Athens
                max_start_days = min(remaining_days[current_city], athens_constraint[1] - 1)
                start_days = min(3, max_start_days)  # Try spending a few days first
                
                if start_days > 0:
                    itinerary.append({"day_range": [day, day + start_days - 1], "place": current_city})
                    remaining_days[current_city] -= start_days
                    day += start_days
                
                # Travel to Athens if possible
                if "Athens" in flights[current_city] and day <= athens_constraint[1]:
                    # Spend time in Athens
                    athens_days = min(remaining_days["Athens"], athens_constraint[1] - day + 1, 6)
                    if athens_days > 0:
                        itinerary.append({"day_range": [day, day + athens_days - 1], "place": "Athens"})
                        remaining_days["Athens"] -= athens_days
                        day += athens_days
                        current_city = "Athens"
                    else:
                        continue  # Can't meet Athens constraint
                else:
                    continue  # Can't reach Athens in time
            
            # Now handle Naples wedding constraint (must be there between day 16-20)
            # We need to ensure we're in Naples for at least some days in 16-20
            # Calculate latest day we can arrive in Naples to meet wedding constraint
            latest_arrival = naples_wedding[1] - remaining_days["Naples"] + 1
            if latest_arrival < naples_wedding[0]:
                latest_arrival = naples_wedding[0]
            
            # Visit other cities until it's time to go to Naples
            while day < latest_arrival and any(v > 0 for v in remaining_days.values()):
                next_city = None
                
                # Try to visit cities that still need days
                for city in visit_order:
                    if remaining_days[city] > 0 and city in flights[current_city] and city != "Naples":
                        next_city = city
                        break
                
                if next_city is None:
                    break  # No valid next city
                
                # Calculate how many days we can spend there
                max_days = min(remaining_days[next_city], latest_arrival - day)
                if max_days <= 0:
                    break
                
                # Travel to next city
                current_city = next_city
                days_to_spend = min(max_days, 3)  # Try spending up to 3 days at a time
                itinerary.append({"day_range": [day, day + days_to_spend - 1], "place": current_city})
                remaining_days[current_city] -= days_to_spend
                day += days_to_spend
            
            # Now go to Naples for wedding
            if current_city != "Naples" and "Naples" in flights[current_city]:
                current_city = "Naples"
            
            # Allocate Naples days for wedding
            if current_city == "Naples":
                wedding_days = min(remaining_days["Naples"], naples_wedding[1] - day + 1)
                if wedding_days > 0:
                    start_day = max(day, naples_wedding[0])
                    end_day = start_day + wedding_days - 1
                    if end_day > naples_wedding[1]:
                        end_day = naples_wedding[1]
                        wedding_days = end_day - start_day + 1
                    
                    if wedding_days > 0:
                        itinerary.append({"day_range": [start_day, end_day], "place": "Naples"})
                        remaining_days["Naples"] -= wedding_days
                        day = end_day + 1
            
            # Fill remaining days with any remaining cities
            while day <= total_days and any(v > 0 for v in remaining_days.values()):
                next_city = None
                for city in visit_order:
                    if remaining_days[city] > 0 and city in flights[current_city]:
                        next_city = city
                        break
                
                if next_city is None:
                    break
                
                current_city = next_city
                days_to_spend = min(remaining_days[current_city], total_days - day + 1)
                itinerary.append({"day_range": [day, day + days_to_spend - 1], "place": current_city})
                remaining_days[current_city] -= days_to_spend
                day += days_to_spend
            
            # Verify all constraints are met
            athens_ok = False
            naples_ok = False
            
            for entry in itinerary:
                if entry["place"] == "Athens":
                    start, end = entry["day_range"]
                    if start <= athens_constraint[1] and end >= athens_constraint[0]:
                        athens_ok = True
                
                if entry["place"] == "Naples":
                    start, end = entry["day_range"]
                    if start <= naples_wedding[1] and end >= naples_wedding[0]:
                        naples_ok = True
            
            if (day > total_days and all(v == 0 for v in remaining_days.values()) 
                and athens_ok and naples_ok:
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