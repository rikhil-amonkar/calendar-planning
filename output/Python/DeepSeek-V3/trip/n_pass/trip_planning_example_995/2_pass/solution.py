import json
from itertools import permutations

def find_itinerary():
    # Define the cities and their required days
    cities = {
        "Oslo": 2,
        "Stuttgart": 3,
        "Venice": 4,
        "Split": 4,
        "Barcelona": 3,
        "Brussels": 3,
        "Copenhagen": 3
    }
    
    # Define the direct flights as a graph
    graph = {
        "Venice": ["Stuttgart", "Barcelona", "Brussels", "Oslo", "Copenhagen"],
        "Stuttgart": ["Venice", "Barcelona", "Copenhagen", "Split"],
        "Oslo": ["Brussels", "Split", "Venice", "Copenhagen", "Barcelona"],
        "Split": ["Copenhagen", "Oslo", "Barcelona", "Stuttgart"],
        "Barcelona": ["Copenhagen", "Venice", "Stuttgart", "Split", "Oslo", "Brussels"],
        "Brussels": ["Oslo", "Venice", "Copenhagen"],
        "Copenhagen": ["Split", "Barcelona", "Brussels", "Oslo", "Venice", "Stuttgart"]
    }
    
    # Fixed constraints
    # Barcelona: Days 1-3 (3 days)
    # Oslo: Must be visited between day 3-4 (2 days)
    # Brussels: Must be visited between day 9-11 (3 days)
    
    # The remaining cities to permute are: Venice, Stuttgart, Split, Copenhagen
    remaining_cities = [city for city in cities.keys() if city not in ["Barcelona", "Oslo", "Brussels"]]
    
    for perm in permutations(remaining_cities):
        itinerary = []
        current_day = 1
        
        # Add Barcelona first (days 1-3)
        itinerary.append({"day_range": f"Day {current_day}-{current_day + 2}", "place": "Barcelona"})
        current_day += 3
        
        # Next is Oslo (days 4-5)
        itinerary.append({"day_range": f"Day {current_day}-{current_day + 1}", "place": "Oslo"})
        current_day += 2
        
        # Now we have days 6-16 remaining (11 days)
        # We need to fit Brussels somewhere between day 9-11 (3 days)
        # And the remaining cities (Venice, Stuttgart, Split, Copenhagen)
        
        # Try inserting Brussels at different positions
        for brussels_pos in range(len(perm) + 1):
            temp_itinerary = itinerary.copy()
            temp_day = current_day
            prev_city = "Oslo"
            valid = True
            total_days = 5  # Already have 3 (Barcelona) + 2 (Oslo)
            
            # Insert the permuted cities with Brussels at brussels_pos
            for i, city in enumerate(perm):
                if i == brussels_pos:
                    # Insert Brussels here
                    if "Brussels" not in graph[prev_city]:
                        valid = False
                        break
                    duration = cities["Brussels"]
                    start_day = temp_day
                    end_day = temp_day + duration - 1
                    # Check Brussels constraint (must cover day 9-11)
                    if not (start_day <= 11 and end_day >= 9):
                        valid = False
                        break
                    temp_itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": "Brussels"})
                    prev_city = "Brussels"
                    temp_day += duration
                    total_days += duration
                
                # Add current city from permutation
                if city not in graph[prev_city]:
                    valid = False
                    break
                duration = cities[city]
                temp_itinerary.append({"day_range": f"Day {temp_day}-{temp_day + duration - 1}", "place": city})
                prev_city = city
                temp_day += duration
                total_days += duration
            
            # Check if we haven't inserted Brussels yet (needs to be at end)
            if valid and "Brussels" not in [entry["place"] for entry in temp_itinerary[2:]]:
                if "Brussels" in graph[prev_city]:
                    duration = cities["Brussels"]
                    start_day = temp_day
                    end_day = temp_day + duration - 1
                    if start_day <= 11 and end_day >= 9:
                        temp_itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": "Brussels"})
                        total_days += duration
                    else:
                        valid = False
                else:
                    valid = False
            
            if not valid:
                continue
            
            # Verify total days is exactly 16
            if total_days == 16:
                # Verify Brussels constraint is met
                brussels_met = False
                for entry in temp_itinerary:
                    if entry["place"] == "Brussels":
                        start, end = map(int, entry["day_range"].split(" ")[1].split("-"))
                        if start <= 11 and end >= 9:
                            brussels_met = True
                            break
                if brussels_met:
                    return {"itinerary": temp_itinerary}
    
    return {"itinerary": []}

result = find_itinerary()
print(json.dumps(result, indent=2))