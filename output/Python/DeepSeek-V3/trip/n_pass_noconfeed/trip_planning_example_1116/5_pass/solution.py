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
    
    # Fixed constraints (city: (start_day, end_day))
    fixed_constraints = {
        "Oslo": (16, 17),     # Must be in Oslo on days 16-17
        "Reykjavik": (9, 13),  # Must be in Reykjavik between days 9-13
        "Munich": (13, 16),    # Must be in Munich between days 13-16
        "Frankfurt": (17, 20)   # Must be in Frankfurt between days 17-20
    }
    
    # Try different orders for the flexible cities
    flexible_cities = [city for city in cities if city not in fixed_constraints]
    
    for perm in permutations(flexible_cities):
        itinerary = []
        current_day = 1
        remaining_days = cities.copy()
        visited_cities = set()
        
        # Visit Oslo first (days 1-2)
        if "Oslo" not in visited_cities and current_day + 1 <= 20:
            itinerary.append({
                "day_range": f"Day {current_day}-{current_day+1}",
                "place": "Oslo"
            })
            remaining_days["Oslo"] = 0
            visited_cities.add("Oslo")
            current_day += 2
        
        # Visit some flexible cities before Reykjavik (days 3-8)
        last_city = "Oslo"
        for city in perm:
            if current_day >= 9:
                break
            if remaining_days[city] > 0 and city != "Reykjavik":
                if city in connections.get(last_city, []):
                    # Add travel day
                    if current_day + 1 > 8:
                        break
                    itinerary.append({
                        "day_range": f"Day {current_day}",
                        "place": f"Travel from {last_city} to {city}"
                    })
                    current_day += 1
                    if current_day > 8:
                        break
                    
                    # Add stay (maximum possible days that fit before day 9)
                    max_possible_days = min(remaining_days[city], 9 - current_day)
                    if max_possible_days > 0:
                        end_day = current_day + max_possible_days - 1
                        itinerary.append({
                            "day_range": f"Day {current_day}-{end_day}",
                            "place": city
                        })
                        remaining_days[city] -= max_possible_days
                        current_day += max_possible_days
                        last_city = city
        
        # Visit Reykjavik (days 9-13)
        if current_day <= 9:
            # Check connection from last city to Reykjavik
            if "Reykjavik" in connections.get(last_city, []):
                # Add travel day if needed (day 9)
                if last_city != "Reykjavik":
                    itinerary.append({
                        "day_range": "Day 9",
                        "place": f"Travel from {last_city} to Reykjavik"
                    })
                    current_day = 10
                else:
                    current_day = 9
                
                # Add Reykjavik stay (days 10-13 or 9-13)
                start_day = current_day
                end_day = 13
                itinerary.append({
                    "day_range": f"Day {start_day}-{end_day}",
                    "place": "Reykjavik"
                })
                remaining_days["Reykjavik"] = 0
                current_day = 14
                last_city = "Reykjavik"
        
        # Travel to Munich (day 14)
        if "Munich" in connections.get(last_city, []):
            itinerary.append({
                "day_range": "Day 14",
                "place": f"Travel from {last_city} to Munich"
            })
            current_day = 15
            last_city = "Munich"
        
        # Visit Munich (days 15-16)
        if current_day <= 16:
            itinerary.append({
                "day_range": "Day 15-16",
                "place": "Munich"
            })
            remaining_days["Munich"] = 0
            current_day = 17
            last_city = "Munich"
        
        # Travel to Oslo (day 16 is already in Munich, need to travel to Oslo)
        if "Oslo" in connections.get(last_city, []):
            itinerary.append({
                "day_range": "Day 16",
                "place": "Travel from Munich to Oslo"
            })
            current_day = 17
            last_city = "Oslo"
        
        # Oslo show (day 17)
        itinerary.append({
            "day_range": "Day 17",
            "place": "Oslo"
        })
        remaining_days["Oslo"] = 0
        current_day = 18
        last_city = "Oslo"
        
        # Travel to Frankfurt (day 18)
        if "Frankfurt" in connections.get(last_city, []):
            itinerary.append({
                "day_range": "Day 18",
                "place": f"Travel from Oslo to Frankfurt"
            })
            current_day = 19
            last_city = "Frankfurt"
        
        # Frankfurt workshop (days 19-20)
        itinerary.append({
            "day_range": "Day 19-20",
            "place": "Frankfurt"
        })
        remaining_days["Frankfurt"] = 0
        current_day = 21
        
        # Check if all cities are visited
        if all(days == 0 for days in remaining_days.values()):
            return {"itinerary": itinerary}
    
    return {"itinerary": []}

# Execute the function and print the result
result = find_itinerary()
print(json.dumps(result, indent=2))