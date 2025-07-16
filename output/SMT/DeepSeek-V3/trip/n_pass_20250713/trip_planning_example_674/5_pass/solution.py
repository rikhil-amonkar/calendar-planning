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

    # Direct flight connections (bidirectional unless noted)
    flight_connections = [
        ("Helsinki", "Reykjavik"),
        ("Budapest", "Warsaw"),
        ("Madrid", "Split"),
        ("Helsinki", "Split"),
        ("Helsinki", "Madrid"),
        ("Helsinki", "Budapest"),
        ("Reykjavik", "Warsaw"),
        ("Helsinki", "Warsaw"),
        ("Madrid", "Budapest"),
        ("Budapest", "Reykjavik"),
        ("Madrid", "Warsaw"),
        ("Warsaw", "Split"),
        ("Reykjavik", "Madrid")  # One-way
    ]

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
    s.add(Or(
        day_city[8] == city_code["Warsaw"],  # Day 9
        day_city[9] == city_code["Warsaw"],  # Day 10
        day_city[10] == city_code["Warsaw"]  # Day 11
    ))

    # Flight constraints
    for i in range(days-1):
        current = day_city[i]
        next_day = day_city[i+1]
        s.add(Or(
            current == next_day,  # Stay in same city
            # Check all possible direct flights
            Or([And(current == city_code[src], next_day == city_code[dst]) 
                for (src, dst) in flight_connections] +
               [And(current == city_code[dst], next_day == city_code[src]) 
                for (src, dst) in flight_connections 
                if (dst, src) not in flight_connections])  # Handle one-way flights
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