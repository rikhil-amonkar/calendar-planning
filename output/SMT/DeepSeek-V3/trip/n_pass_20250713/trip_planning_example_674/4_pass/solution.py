from z3 import *
import json

def solve_itinerary():
    # Cities and their required days
    cities = ["Helsinki", "Warsaw", "Madrid", "Split", "Reykjavik", "Budapest"]
    required_days = {
        "Helsinki": 2,
        "Warsaw": 3,
        "Madrid": 4,
        "Split": 4,
        "Reykjavik": 2,
        "Budapest": 4
    }

    # Direct flights (bidirectional except Reykjavik-Madrid is one-way)
    direct_flights = {
        "Helsinki": ["Reykjavik", "Split", "Madrid", "Budapest", "Warsaw"],
        "Warsaw": ["Budapest", "Reykjavik", "Helsinki", "Madrid", "Split"],
        "Madrid": ["Split", "Helsinki", "Budapest", "Warsaw"],
        "Split": ["Madrid", "Helsinki", "Warsaw"],
        "Reykjavik": ["Helsinki", "Warsaw", "Budapest"],  # Can fly to Madrid but not back
        "Budapest": ["Warsaw", "Madrid", "Helsinki", "Reykjavik"],
        "Madrid": ["Reykjavik"]  # One-way from Reykjavik
    }

    # Create solver
    s = Solver()

    # Day variables (1-based)
    days = 14
    day_city = [Int(f"day_{i}") for i in range(days)]

    # City encodings
    city_code = {city: i for i, city in enumerate(cities)}
    code_city = {i: city for i, city in enumerate(cities)}

    # Each day must be a valid city code
    for day in day_city:
        s.add(day >= 0, day < len(cities))

    # Fixed constraints
    # Helsinki on days 1-2 (workshop)
    s.add(day_city[0] == city_code["Helsinki"])
    s.add(day_city[1] == city_code["Helsinki"])

    # Reykjavik between days 8-9 (friend meeting)
    s.add(Or(
        day_city[7] == city_code["Reykjavik"],  # Day 8
        day_city[8] == city_code["Reykjavik"]   # Day 9
    ))

    # Warsaw between days 9-11 (relatives)
    # We'll make this more flexible by requiring at least one day in Warsaw during 9-11
    s.add(Or(
        day_city[8] == city_code["Warsaw"],
        day_city[9] == city_code["Warsaw"],
        day_city[10] == city_code["Warsaw"]
    ))

    # Flight constraints - more flexible approach
    for i in range(days-1):
        current = day_city[i]
        next_day = day_city[i+1]
        s.add(Or(
            current == next_day,  # Stay in same city
            # Check all possible direct flights
            Or(
                And(current == city_code["Helsinki"], next_day == city_code["Reykjavik"]),
                And(current == city_code["Helsinki"], next_day == city_code["Split"]),
                And(current == city_code["Helsinki"], next_day == city_code["Madrid"]),
                And(current == city_code["Helsinki"], next_day == city_code["Budapest"]),
                And(current == city_code["Helsinki"], next_day == city_code["Warsaw"]),
                And(current == city_code["Warsaw"], next_day == city_code["Budapest"]),
                And(current == city_code["Warsaw"], next_day == city_code["Reykjavik"]),
                And(current == city_code["Warsaw"], next_day == city_code["Helsinki"]),
                And(current == city_code["Warsaw"], next_day == city_code["Madrid"]),
                And(current == city_code["Warsaw"], next_day == city_code["Split"]),
                And(current == city_code["Madrid"], next_day == city_code["Split"]),
                And(current == city_code["Madrid"], next_day == city_code["Helsinki"]),
                And(current == city_code["Madrid"], next_day == city_code["Budapest"]),
                And(current == city_code["Madrid"], next_day == city_code["Warsaw"]),
                And(current == city_code["Split"], next_day == city_code["Madrid"]),
                And(current == city_code["Split"], next_day == city_code["Helsinki"]),
                And(current == city_code["Split"], next_day == city_code["Warsaw"]),
                And(current == city_code["Reykjavik"], next_day == city_code["Helsinki"]),
                And(current == city_code["Reykjavik"], next_day == city_code["Warsaw"]),
                And(current == city_code["Reykjavik"], next_day == city_code["Budapest"]),
                And(current == city_code["Reykjavik"], next_day == city_code["Madrid"]),
                And(current == city_code["Budapest"], next_day == city_code["Warsaw"]),
                And(current == city_code["Budapest"], next_day == city_code["Madrid"]),
                And(current == city_code["Budapest"], next_day == city_code["Helsinki"]),
                And(current == city_code["Budapest"], next_day == city_code["Reykjavik"])
            )
        ))

    # Count days in each city
    for city, days_needed in required_days.items():
        count = Sum([If(day_city[i] == city_code[city], 1, 0) for i in range(days)])
        s.add(count == days_needed)

    # Solve
    if s.check() == sat:
        m = s.model()
        itinerary = []
        current_place = code_city[m.evaluate(day_city[0]).as_long()]
        start_day = 1

        for i in range(1, days):
            place = code_city[m.evaluate(day_city[i]).as_long()]
            if place != current_place:
                # Add stay for current place
                if start_day == i:
                    itinerary.append({"day_range": f"Day {start_day}", "place": current_place})
                else:
                    itinerary.append({"day_range": f"Day {start_day}-{i}", "place": current_place})
                # Add flight day
                itinerary.append({"day_range": f"Day {i+1}", "place": current_place})
                itinerary.append({"day_range": f"Day {i+1}", "place": place})
                current_place = place
                start_day = i+1

        # Add last stay
        if start_day <= days:
            if start_day == days:
                itinerary.append({"day_range": f"Day {start_day}", "place": current_place})
            else:
                itinerary.append({"day_range": f"Day {start_day}-{days}", "place": current_place})

        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

result = solve_itinerary()
print(json.dumps(result, indent=2))