import json
from itertools import product

def solve_itinerary():
    cities = ["Oslo", "Reykjavik", "Stockholm", "Munich", "Frankfurt", "Barcelona", "Bucharest", "Split"]
    city_indices = {city: idx for idx, city in enumerate(cities)}
    
    direct_flights = {
        "Reykjavik": ["Munich", "Oslo", "Frankfurt", "Barcelona", "Stockholm"],
        "Munich": ["Reykjavik", "Frankfurt", "Bucharest", "Oslo", "Stockholm", "Barcelona", "Split"],
        "Frankfurt": ["Munich", "Oslo", "Barcelona", "Reykjavik", "Bucharest", "Stockholm", "Split"],
        "Oslo": ["Split", "Reykjavik", "Frankfurt", "Bucharest", "Stockholm", "Barcelona", "Munich"],
        "Bucharest": ["Munich", "Barcelona", "Oslo", "Frankfurt"],
        "Barcelona": ["Bucharest", "Frankfurt", "Reykjavik", "Stockholm", "Split", "Oslo", "Munich"],
        "Stockholm": ["Barcelona", "Reykjavik", "Munich", "Oslo", "Frankfurt", "Split"],
        "Split": ["Oslo", "Barcelona", "Stockholm", "Frankfurt", "Munich"]
    }
    
    required_days = {
        "Oslo": 2,
        "Reykjavik": 5,
        "Stockholm": 4,
        "Munich": 4,
        "Frankfurt": 4,
        "Barcelona": 3,
        "Bucharest": 2,
        "Split": 3
    }
    
    total_days = 20
    
    # Fixed constraints
    fixed_days = {
        15: "Oslo",  # Day 16 (0-based index 15)
        16: "Oslo"   # Day 17 (0-based index 16)
    }
    
    # Range constraints
    range_constraints = [
        (8, 13, "Reykjavik"),   # Days 9-13 must include Reykjavik
        (12, 16, "Munich"),      # Days 13-16 must include Munich
        (16, 20, "Frankfurt")    # Days 17-20 must include Frankfurt
    ]
    
    # Initialize itinerary
    itinerary = [None] * total_days
    
    # Apply fixed days
    for day, city in fixed_days.items():
        itinerary[day] = city
    
    # Backtracking function to fill the itinerary
    def backtrack(day, city_counts, last_city):
        if day == total_days:
            # Check all range constraints
            for start, end, city in range_constraints:
                if city not in itinerary[start:end]:
                    return None
            # Check all cities have required days
            for city, count in required_days.items():
                if itinerary.count(city) != count:
                    return None
            return itinerary.copy()
        
        # If day is already fixed
        if itinerary[day] is not None:
            return backtrack(day + 1, city_counts, itinerary[day])
        
        # Try all possible cities
        for city in cities:
            # Check if we've already used up this city's days
            if city_counts[city] >= required_days[city]:
                continue
            
            # Check flight constraint if not first day
            if day > 0 and last_city != city and city not in direct_flights[last_city]:
                continue
            
            # Assign city to this day
            itinerary[day] = city
            city_counts[city] += 1
            
            # Recurse
            result = backtrack(day + 1, city_counts, city)
            if result is not None:
                return result
            
            # Backtrack
            itinerary[day] = None
            city_counts[city] -= 1
        
        return None
    
    # Initialize city counts
    city_counts = {city: 0 for city in cities}
    for day, city in fixed_days.items():
        city_counts[city] += 1
    
    # Start backtracking from day 0
    result = backtrack(0, city_counts, None)
    
    if result is None:
        return {"error": "No valid itinerary found"}
    
    # Format the itinerary
    formatted_itinerary = []
    current_city = result[0]
    start_day = 1
    
    for day in range(1, total_days):
        if result[day] != result[day - 1]:
            # Flight day - add both cities
            formatted_itinerary.append({"day_range": f"Day {start_day}-{day}", "place": current_city})
            formatted_itinerary.append({"day_range": f"Day {day + 1}", "place": result[day - 1]})
            formatted_itinerary.append({"day_range": f"Day {day + 1}", "place": result[day]})
            start_day = day + 1
            current_city = result[day]
    
    # Add last segment
    formatted_itinerary.append({"day_range": f"Day {start_day}-{total_days}", "place": current_city})
    
    # Merge consecutive same-city entries
    merged_itinerary = []
    i = 0
    while i < len(formatted_itinerary):
        current = formatted_itinerary[i]
        if i + 1 < len(formatted_itinerary) and current["place"] == formatted_itinerary[i + 1]["place"]:
            # Merge entries
            start = int(current["day_range"].split('-')[0].replace("Day ", ""))
            end = int(formatted_itinerary[i + 1]["day_range"].split('-')[-1].replace("Day ", ""))
            merged_entry = {"day_range": f"Day {start}-{end}", "place": current["place"]}
            merged_itinerary.append(merged_entry)
            i += 2
        else:
            merged_itinerary.append(current)
            i += 1
    
    return {"itinerary": merged_itinerary}

# Execute and print the result
result = solve_itinerary()
print(json.dumps(result, indent=2))