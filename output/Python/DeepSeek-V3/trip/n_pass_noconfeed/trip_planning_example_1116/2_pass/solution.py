import json
from itertools import permutations

def find_itinerary():
    # Define the cities and their required days
    cities = {
        "Oslo": 2,
        "Reykjavik": 5,
        "Stockholm": 4,
        "Munich": 4,
        "Frankfurt": 4,
        "Barcelona": 3,
        "Bucharest": 2,
        "Split": 3
    }
    
    # Define the direct flight connections
    connections = {
        "Reykjavik": ["Munich", "Oslo", "Frankfurt", "Barcelona", "Stockholm"],
        "Munich": ["Reykjavik", "Frankfurt", "Bucharest", "Oslo", "Stockholm", "Split", "Barcelona"],
        "Frankfurt": ["Munich", "Oslo", "Barcelona", "Reykjavik", "Bucharest", "Stockholm", "Split"],
        "Oslo": ["Split", "Reykjavik", "Frankfurt", "Bucharest", "Barcelona", "Stockholm", "Munich"],
        "Bucharest": ["Munich", "Barcelona", "Oslo", "Frankfurt"],
        "Barcelona": ["Bucharest", "Frankfurt", "Reykjavik", "Stockholm", "Split", "Oslo", "Munich"],
        "Stockholm": ["Barcelona", "Reykjavik", "Split", "Munich", "Oslo", "Frankfurt"],
        "Split": ["Oslo", "Barcelona", "Stockholm", "Frankfurt", "Munich"]
    }
    
    # Fixed constraints
    fixed_constraints = {
        "Oslo": (16, 17),    # Annual show in Oslo from day 16 to 17
        "Reykjavik": (9, 13), # Meet friend in Reykjavik between day 9 and 13
        "Munich": (13, 16),   # Visit relatives in Munich between day 13 and 16
        "Frankfurt": (17, 20)  # Workshop in Frankfurt between day 17 and 20
    }
    
    # We'll prioritize cities with fixed constraints first
    constrained_cities = ["Reykjavik", "Munich", "Frankfurt", "Oslo"]
    
    # Try different starting points
    for start_city in ["Reykjavik", "Munich", "Frankfurt", "Oslo", "Barcelona", "Stockholm"]:
        itinerary = []
        current_day = 1
        remaining_days = cities.copy()
        visited = set()
        
        # First visit to Oslo (2 days) before the show
        if "Oslo" in remaining_days and remaining_days["Oslo"] > 0:
            # Find earliest possible time to visit Oslo for 2 days before day 16
            if current_day <= 14:  # 14-15
                itinerary.append({
                    "day_range": f"Day {current_day}-{current_day+1}",
                    "place": "Oslo"
                })
                remaining_days["Oslo"] -= 2
                current_day += 2
                visited.add("Oslo")
        
        # Visit Reykjavik between day 9-13
        if "Reykjavik" in remaining_days and remaining_days["Reykjavik"] > 0:
            start_day = max(9, current_day)
            if start_day <= 9:  # Can start at day 9
                end_day = start_day + 4  # 9-13 (5 days)
                if end_day <= 13:
                    itinerary.append({
                        "day_range": f"Day {start_day}-{end_day}",
                        "place": "Reykjavik"
                    })
                    remaining_days["Reykjavik"] = 0
                    current_day = end_day + 1
                    visited.add("Reykjavik")
        
        # Visit Munich between day 13-16
        if "Munich" in remaining_days and remaining_days["Munich"] > 0:
            start_day = max(13, current_day)
            end_day = start_day + 3  # 4 days
            if end_day <= 16:
                itinerary.append({
                    "day_range": f"Day {start_day}-{end_day}",
                    "place": "Munich"
                })
                remaining_days["Munich"] = 0
                current_day = end_day + 1
                visited.add("Munich")
        
        # Oslo show (must be day 16-17)
        if "Oslo" in remaining_days and remaining_days["Oslo"] > 0:
            itinerary.append({
                "day_range": "Day 16-17",
                "place": "Oslo"
            })
            remaining_days["Oslo"] = 0
            current_day = 18
            visited.add("Oslo")
        
        # Frankfurt workshop (day 17-20)
        if "Frankfurt" in remaining_days and remaining_days["Frankfurt"] > 0:
            start_day = max(17, current_day)
            end_day = start_day + 3  # 4 days
            if end_day <= 20:
                itinerary.append({
                    "day_range": f"Day {start_day}-{end_day}",
                    "place": "Frankfurt"
                })
                remaining_days["Frankfurt"] = 0
                current_day = end_day + 1
                visited.add("Frankfurt")
        
        # Now visit remaining cities (Barcelona, Stockholm, Bucharest, Split)
        remaining_to_visit = [city for city in cities if remaining_days[city] > 0]
        
        # Try to visit them in an order that fits the remaining days
        for city in remaining_to_visit:
            if current_day > 20:
                break
            if remaining_days[city] > 0:
                duration = remaining_days[city]
                end_day = current_day + duration - 1
                if end_day <= 20:
                    # Check if we can get to this city from previous location
                    prev_city = itinerary[-1]["place"] if itinerary else start_city
                    if prev_city.startswith("Travel from"):
                        prev_city = prev_city.split(" to ")[1]
                    
                    if city in connections.get(prev_city, []):
                        # Add travel day if needed
                        if prev_city != city:
                            itinerary.append({
                                "day_range": f"Day {current_day}",
                                "place": f"Travel from {prev_city} to {city}"
                            })
                            current_day += 1
                            end_day += 1
                        
                        if end_day <= 20:
                            itinerary.append({
                                "day_range": f"Day {current_day}-{end_day}",
                                "place": city
                            })
                            remaining_days[city] = 0
                            current_day = end_day + 1
        
        # Check if all cities are visited and all days are used
        if all(days == 0 for days in remaining_days.values()) and current_day > 20:
            # Verify all fixed constraints are met
            valid = True
            for city, (start, end) in fixed_constraints.items():
                found = False
                for entry in itinerary:
                    if entry["place"] == city:
                        day_range = entry["day_range"][4:].split("-")
                        day_start = int(day_range[0])
                        day_end = int(day_range[1]) if len(day_range) > 1 else day_start
                        if day_start <= end and day_end >= start:
                            found = True
                            break
                if not found:
                    valid = False
                    break
            
            if valid:
                return {"itinerary": itinerary}
    
    return {"itinerary": []}

# Execute the function and print the result
result = find_itinerary()
print(json.dumps(result, indent=2))