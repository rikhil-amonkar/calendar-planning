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

    # Direct flights (bidirectional except where noted)
    direct_flights = {
        "Helsinki": ["Reykjavik", "Split", "Madrid", "Budapest", "Warsaw"],
        "Warsaw": ["Budapest", "Reykjavik", "Helsinki", "Madrid", "Split"],
        "Madrid": ["Split", "Helsinki", "Budapest", "Warsaw"],
        "Split": ["Madrid", "Helsinki", "Warsaw"],
        "Reykjavik": ["Helsinki", "Warsaw", "Budapest", "Madrid"],
        "Budapest": ["Warsaw", "Madrid", "Helsinki", "Reykjavik"]
    }

    # Create solver
    s = Solver()

    # Day variables (1-based)
    days = 14
    day_city = [Int(f"day_{i}") for i in range(1, days+1)]

    # City encodings
    city_code = {city: i for i, city in enumerate(cities)}
    code_city = {i: city for i, city in enumerate(cities)}

    # Each day must be a valid city code
    for day in day_city:
        s.add(day >= 0, day < len(cities))

    # Fixed constraints
    # Helsinki on days 1-2
    s.add(day_city[0] == city_code["Helsinki"])
    s.add(day_city[1] == city_code["Helsinki"])

    # Reykjavik between days 8-9
    s.add(Or(
        day_city[7] == city_code["Reykjavik"],
        day_city[8] == city_code["Reykjavik"]
    ))

    # Warsaw between days 9-11
    s.add(Or(
        day_city[8] == city_code["Warsaw"],
        day_city[9] == city_code["Warsaw"],
        day_city[10] == city_code["Warsaw"]
    ))

    # Flight constraints
    for i in range(days-1):
        current = day_city[i]
        next_day = day_city[i+1]
        s.add(Or(
            current == next_day,  # Stay in same city
            # Or take a direct flight
            Or([And(current == city_code[city], next_day == city_code[adj])
                for city in direct_flights 
                for adj in direct_flights[city] 
                if adj in city_code])
        ))

    # Count days in each city
    for city in cities:
        count = Sum([If(day_city[i] == city_code[city], 1, 0) for i in range(days)])
        s.add(count == required_days[city])

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