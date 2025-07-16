from z3 import *
import json

def solve_itinerary():
    # Cities
    cities = ["Helsinki", "Warsaw", "Madrid", "Split", "Reykjavik", "Budapest"]
    
    # Direct flights (undirected, but we'll treat as bidirectional)
    direct_flights = {
        "Helsinki": ["Reykjavik", "Split", "Madrid", "Budapest", "Warsaw"],
        "Warsaw": ["Budapest", "Reykjavik", "Helsinki", "Madrid", "Split"],
        "Madrid": ["Split", "Helsinki", "Budapest", "Warsaw"],
        "Split": ["Madrid", "Helsinki", "Warsaw"],
        "Reykjavik": ["Helsinki", "Warsaw", "Budapest", "Madrid"],
        "Budapest": ["Warsaw", "Madrid", "Helsinki", "Reykjavik"]
    }
    
    # Correcting the direct_flights for any typos (e.g., "Helsinki" vs "Helsinki")
    # Reconstructing the direct_flights properly based on the problem statement
    direct_flights = {
        "Helsinki": ["Reykjavik", "Split", "Madrid", "Budapest", "Warsaw"],
        "Warsaw": ["Budapest", "Reykjavik", "Helsinki", "Madrid", "Split"],
        "Madrid": ["Split", "Helsinki", "Budapest", "Warsaw"],
        "Split": ["Madrid", "Helsinki", "Warsaw"],
        "Reykjavik": ["Helsinki", "Warsaw", "Budapest", "Madrid"],
        "Budapest": ["Warsaw", "Madrid", "Helsinki", "Reykjavik"]
    }
    
    # Total days
    total_days = 14
    
    # Create a solver instance
    s = Solver()
    
    # Variables: for each day, which city are we in?
    # day_city[i] represents the city on day i+1 (days are 1-based)
    day_city = [Int(f"day_{i}_city") for i in range(total_days)]
    
    # City encodings
    city_to_code = {city: idx for idx, city in enumerate(cities)}
    code_to_city = {idx: city for idx, city in enumerate(cities)}
    
    # Add constraints: each day_city must be a valid city code
    for dc in day_city:
        s.add(And(dc >= 0, dc < len(cities)))
    
    # Constraints for city stays:
    # Helsinki: 2 days, including day 1-2 for workshop
    s.add(day_city[0] == city_to_code["Helsinki"])  # Day 1
    s.add(day_city[1] == city_to_code["Helsinki"])  # Day 2
    
    # Warsaw: 3 days, including day 9-11 for relatives
    # So Warsaw must be visited on at least one of days 9, 10, or 11
    # But total days in Warsaw is 3. So the 3 days must include these.
    # We'll need to find a 3-day contiguous block that includes at least one of 9-11.
    # For simplicity, we'll assume that Warsaw is visited on days 9,10,11 (but the total days in Warsaw is 3, so possibly other days)
    # Alternatively, the 3 days could be, say, 9,10,11, but the problem says "between day 9 and day 11", which could mean days 9,10,11.
    # Assuming that the 3 days include days 9,10,11.
    s.add(Or(
        day_city[8] == city_to_code["Warsaw"],  # Day 9
        day_city[9] == city_to_code["Warsaw"],  # Day 10
        day_city[10] == city_to_code["Warsaw"]  # Day 11
    ))
    
    # Reykjavik: 2 days, including day 8-9 for meeting friend
    s.add(Or(
        day_city[7] == city_to_code["Reykjavik"],  # Day 8
        day_city[8] == city_to_code["Reykjavik"]   # Day 9
    ))
    
    # Total days per city
    city_days = {
        "Helsinki": 2,
        "Warsaw": 3,
        "Madrid": 4,
        "Split": 4,
        "Reykjavik": 2,
        "Budapest": 4
    }
    # Correcting the city names in city_days
    city_days = {
        "Helsinki": 2,
        "Warsaw": 3,
        "Madrid": 4,
        "Split": 4,
        "Reykjavik": 2,
        "Budapest": 4
    }
    
    for city, days in city_days.items():
        s.add(Sum([If(day_city[i] == city_to_code[city], 1, 0) for i in range(total_days)]) == days)
    
    # Flight constraints: consecutive days must be either the same city or connected by a direct flight
    for i in range(total_days - 1):
        current_city = day_city[i]
        next_city = day_city[i+1]
        # Either stay in the same city or move to a directly connected city
        s.add(Or(
            current_city == next_city,
            And(current_city != next_city,
                Or([And(current_city == city_to_code[city], next_city == city_to_code[adj])
                    for city in direct_flights
                    for adj in direct_flights[city]
                    if adj in city_to_code]))
        ))
    
    # Check if the problem is satisfiable
    if s.check() == sat:
        m = s.model()
        # Decode the solution
        itinerary_days = []
        for i in range(total_days):
            city_code = m.evaluate(day_city[i]).as_long()
            itinerary_days.append(code_to_city[city_code])
        
        # Now, generate the itinerary in the required JSON format
        itinerary = []
        current_place = itinerary_days[0]
        start_day = 1
        
        for i in range(1, total_days):
            if itinerary_days[i] == current_place:
                continue
            else:
                end_day = i
                if start_day == end_day:
                    day_str = f"Day {start_day}"
                else:
                    day_str = f"Day {start_day}-{end_day}"
                itinerary.append({"day_range": day_str, "place": current_place})
                # Flight day: add the departure and arrival
                itinerary.append({"day_range": f"Day {i}", "place": current_place})
                itinerary.append({"day_range": f"Day {i}", "place": itinerary_days[i]})
                current_place = itinerary_days[i]
                start_day = i + 1
        
        # Add the last stay
        if start_day <= total_days:
            if start_day == total_days:
                day_str = f"Day {start_day}"
            else:
                day_str = f"Day {start_day}-{total_days}"
            itinerary.append({"day_range": day_str, "place": current_place})
        
        # Now, we need to ensure that for flight days, both departure and arrival are listed.
        # The above code may not capture all cases, so we need to adjust.
        # Let me re-process the itinerary_days to generate the correct JSON.
        
        # Reconstruct the itinerary properly.
        itinerary = []
        prev_city = None
        for day in range(1, total_days + 1):
            current_city = itinerary_days[day - 1]
            if prev_city is None:
                prev_city = current_city
                start_day = day
            else:
                if current_city != prev_city:
                    # Add the stay in prev_city up to day-1
                    if start_day == day - 1:
                        itinerary.append({"day_range": f"Day {start_day}", "place": prev_city})
                    else:
                        itinerary.append({"day_range": f"Day {start_day}-{day - 1}", "place": prev_city})
                    # Add the flight day
                    itinerary.append({"day_range": f"Day {day}", "place": prev_city})
                    itinerary.append({"day_range": f"Day {day}", "place": current_city})
                    prev_city = current_city
                    start_day = day + 1
                else:
                    pass
        # Add the last stay
        if start_day <= total_days:
            if start_day == total_days:
                itinerary.append({"day_range": f"Day {start_day}", "place": prev_city})
            else:
                itinerary.append({"day_range": f"Day {start_day}-{total_days}", "place": prev_city})
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Solve and print the itinerary
result = solve_itinerary()
print(json.dumps(result, indent=2))