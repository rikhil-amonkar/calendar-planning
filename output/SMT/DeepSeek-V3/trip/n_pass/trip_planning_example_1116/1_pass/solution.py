from z3 import *
import json

def solve_itinerary():
    # Cities involved
    cities = ["Oslo", "Reykjavik", "Stockholm", "Munich", "Frankfurt", "Barcelona", "Bucharest", "Split"]
    
    # Direct flights as adjacency list
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
    
    # Required days in each city
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
    
    # Total days
    total_days = 20
    
    # Create a Z3 solver instance
    s = Solver()
    
    # Variables: day_to_city[d] is the city visited on day d (1-based)
    day_to_city = [Int(f"day_{d}_city") for d in range(1, total_days + 1)]
    
    # Map cities to integers
    city_to_int = {city: idx for idx, city in enumerate(cities)}
    int_to_city = {idx: city for idx, city in enumerate(cities)}
    
    # Constraint: each day_to_city must be a valid city index
    for d in range(total_days):
        s.add(day_to_city[d] >= 0, day_to_city[d] < len(cities))
    
    # Constraint: total days per city matches required_days
    for city in cities:
        city_idx = city_to_int[city]
        s.add(Sum([If(day_to_city[d] == city_idx, 1, 0) for d in range(total_days)]) == required_days[city]
    
    # Specific constraints:
    # Oslo on days 16-17 (indices 15 and 16 in 0-based)
    oslo_idx = city_to_int["Oslo"]
    s.add(day_to_city[15] == oslo_idx)  # Day 16
    s.add(day_to_city[16] == oslo_idx)  # Day 17
    
    # Reykjavik between day 9-13 (indices 8-12 in 0-based)
    reykjavik_idx = city_to_int["Reykjavik"]
    s.add(Or([day_to_city[d] == reykjavik_idx for d in range(8, 13)]))
    
    # Munich between day 13-16 (indices 12-15 in 0-based)
    munich_idx = city_to_int["Munich"]
    s.add(Or([day_to_city[d] == munich_idx for d in range(12, 16)]))
    
    # Frankfurt between day 17-20 (indices 16-19 in 0-based)
    frankfurt_idx = city_to_int["Frankfurt"]
    s.add(Or([day_to_city[d] == frankfurt_idx for d in range(16, 20)]))
    
    # Flight constraints: consecutive days must be either same city or connected by direct flight
    for d in range(total_days - 1):
        current_city = day_to_city[d]
        next_city = day_to_city[d + 1]
        # Either stay in the same city or move to a directly connected city
        same_city = current_city == next_city
        possible_flights = []
        for city in cities:
            current_city_name = int_to_city[current_city]
            next_city_name = int_to_city[next_city]
            if next_city_name in direct_flights.get(current_city_name, []):
                possible_flights.append(And(current_city == city_to_int[current_city_name], next_city == city_to_int[next_city_name]))
        s.add(Or(same_city, Or(possible_flights)))
    
    # Check if the solver can find a solution
    if s.check() == sat:
        m = s.model()
        itinerary = []
        current_city = None
        start_day = 1
        # Generate the itinerary day by day
        for d in range(total_days):
            city_idx = m.evaluate(day_to_city[d]).as_long()
            city = int_to_city[city_idx]
            itinerary.append({"day_range": f"Day {d + 1}", "place": city})
        
        # Process the itinerary to combine consecutive days in the same city
        optimized_itinerary = []
        i = 0
        while i < total_days:
            current_city = itinerary[i]["place"]
            start = i + 1
            end = i + 1
            while end < total_days and itinerary[end]["place"] == current_city:
                end += 1
            if start == end:
                optimized_itinerary.append({"day_range": f"Day {start}", "place": current_city})
            else:
                optimized_itinerary.append({"day_range": f"Day {start}-{end}", "place": current_city})
                # Add individual days for flight days (if any)
                # But since flights are between days, this might not be necessary here
            i = end
        
        # Now, handle flight days: for consecutive different cities, insert both on the transition day
        final_itinerary = []
        prev_city = None
        prev_day = None
        for entry in optimized_itinerary:
            day_range = entry["day_range"]
            place = entry["place"]
            if '-' in day_range:
                start_day, end_day = map(int, day_range.replace("Day ", "").split('-'))
                if prev_city is not None and prev_city != place:
                    # Flight day is start_day
                    # Add the departure city for start_day
                    final_itinerary.append({"day_range": f"Day {start_day}", "place": prev_city})
                    # Add the arrival city for start_day
                    final_itinerary.append({"day_range": f"Day {start_day}", "place": place})
                # Add the stay entry
                final_itinerary.append(entry)
                prev_city = place
                prev_day = end_day
            else:
                day = int(day_range.replace("Day ", ""))
                if prev_city is not None and prev_city != place:
                    # Flight day is day
                    final_itinerary.append({"day_range": f"Day {day}", "place": prev_city})
                    final_itinerary.append({"day_range": f"Day {day}", "place": place})
                else:
                    final_itinerary.append(entry)
                prev_city = place
                prev_day = day
        
        # Now, re-process to merge consecutive same-city entries after flight handling
        merged_itinerary = []
        i = 0
        n = len(final_itinerary)
        while i < n:
            current = final_itinerary[i]
            if i + 1 < n and current["place"] == final_itinerary[i + 1]["place"]:
                # Merge consecutive same-city entries
                start_day = int(current["day_range"].replace("Day ", "").split('-')[0])
                j = i + 1
                while j < n and final_itinerary[j]["place"] == current["place"]:
                    j += 1
                end_day = int(final_itinerary[j - 1]["day_range"].replace("Day ", "").split('-')[-1])
                merged_entry = {"day_range": f"Day {start_day}-{end_day}", "place": current["place"]}
                merged_itinerary.append(merged_entry)
                i = j
            else:
                merged_itinerary.append(current)
                i += 1
        
        return {"itinerary": merged_itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Execute and print the result
result = solve_itinerary()
print(json.dumps(result, indent=2))