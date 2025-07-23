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
    
    # Generate all possible permutations of the 4 cities
    for perm in permutations(cities.keys()):
        # Try all possible starting cities
        for start_city in cities.keys():
            itinerary = []
            current_city = start_city
            remaining_days = {city: cities[city] for city in cities}
            day = 1
            
            # Initialize itinerary with starting city
            itinerary.append({"day_range": f"Day {day}", "place": current_city})
            remaining_days[current_city] -= 1
            
            # Proceed until all days are allocated
            while day < total_days:
                # Check if we need to move to another city
                if remaining_days[current_city] == 0:
                    # Find next city to visit
                    next_city = None
                    for city in perm:
                        if city != current_city and remaining_days[city] > 0 and city in flights[current_city]:
                            next_city = city
                            break
                    
                    if next_city is None:
                        break  # No valid next city
                    
                    # Move to next city (same day counts for both)
                    day += 1
                    if day > total_days:
                        break
                    itinerary[-1]["day_range"] = f"Day {int(itinerary[-1]['day_range'].split(' ')[1].split('-')[0])}-{day-1}"
                    itinerary.append({"day_range": f"Day {day}", "place": next_city})
                    remaining_days[next_city] -= 1
                    current_city = next_city
                else:
                    # Stay in current city
                    day += 1
                    if day > total_days:
                        break
                    itinerary[-1]["day_range"] = f"Day {int(itinerary[-1]['day_range'].split(' ')[1].split('-')[0])}-{day}"
                    remaining_days[current_city] -= 1
            
            # Check if all days are allocated and constraints are satisfied
            if day == total_days and all(v == 0 for v in remaining_days.values()):
                # Check Athens constraint
                athens_ok = False
                for entry in itinerary:
                    days = entry["day_range"].split(' ')[1].split('-')
                    start_day = int(days[0])
                    end_day = int(days[-1])
                    if entry["place"] == "Athens" and start_day <= athens_constraint[1] and end_day >= athens_constraint[0]:
                        athens_ok = True
                        break
                
                # Check Naples wedding constraint
                naples_ok = False
                for entry in itinerary:
                    days = entry["day_range"].split(' ')[1].split('-')
                    start_day = int(days[0])
                    end_day = int(days[-1])
                    if entry["place"] == "Naples" and start_day <= naples_wedding[1] and end_day >= naples_wedding[0]:
                        naples_ok = True
                        break
                
                if athens_ok and naples_ok:
                    # Consolidate consecutive days in the same city
                    consolidated_itinerary = []
                    current_entry = itinerary[0]
                    for entry in itinerary[1:]:
                        if entry["place"] == current_entry["place"]:
                            # Merge
                            current_start = int(current_entry["day_range"].split(' ')[1].split('-')[0])
                            current_end = int(entry["day_range"].split(' ')[1].split('-')[-1])
                            current_entry["day_range"] = f"Day {current_start}-{current_end}"
                        else:
                            consolidated_itinerary.append(current_entry)
                            current_entry = entry
                    consolidated_itinerary.append(current_entry)
                    
                    return {"itinerary": consolidated_itinerary}
    
    return {"itinerary": []}

result = calculate_itinerary()
print(json.dumps(result, indent=2))