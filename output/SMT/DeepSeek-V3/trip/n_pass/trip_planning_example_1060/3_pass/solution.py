from z3 import And, Or, Implies, Sum, If, Int, Solver, sat
import json

def solve_itinerary():
    cities = ["Stuttgart", "Istanbul", "Vilnius", "Seville", "Geneva", "Valencia", "Munich", "Reykjavik"]
    days = 25
    city_vars = [Int(f"day_{i}_city") for i in range(1, days + 1)]
    s = Solver()

    for var in city_vars:
        s.add(var >= 0, var < len(cities))

    direct_flights = {
        "Geneva": ["Istanbul", "Munich", "Valencia"],
        "Istanbul": ["Geneva", "Stuttgart", "Valencia", "Vilnius", "Munich"],
        "Reykjavik": ["Munich", "Stuttgart"],
        "Stuttgart": ["Valencia", "Istanbul", "Reykjavik"],
        "Munich": ["Reykjavik", "Geneva", "Vilnius", "Seville", "Istanbul"],
        "Valencia": ["Stuttgart", "Seville", "Istanbul", "Geneva", "Munich"],
        "Vilnius": ["Istanbul", "Munich"],
        "Seville": ["Valencia", "Munich"]
    }

    allowed_transitions = []
    for c1 in direct_flights:
        for c2 in direct_flights[c1]:
            allowed_transitions.append((cities.index(c1), cities.index(c2)))

    for i in range(days - 1):
        current_city_var = city_vars[i]
        next_city_var = city_vars[i + 1]
        s.add(Implies(current_city_var != next_city_var,
                     Or([And(current_city_var == a, next_city_var == b) for a, b in allowed_transitions])))

    # Stuttgart: 4 days total, conference on day 4 and 7
    s.add(city_vars[3] == cities.index("Stuttgart"))  # Day 4
    s.add(city_vars[6] == cities.index("Stuttgart"))  # Day 7
    stuttgart_days = Sum([If(city_vars[i] == cities.index("Stuttgart"), 1, 0) for i in range(days)])
    s.add(stuttgart_days == 4)

    # Istanbul: 4 days, days 19-22
    for i in range(18, 22):
        s.add(city_vars[i] == cities.index("Istanbul"))
    istanbul_days = Sum([If(city_vars[i] == cities.index("Istanbul"), 1, 0) for i in range(days)])
    s.add(istanbul_days == 4)

    # Vilnius: 4 days
    vilnius_days = Sum([If(city_vars[i] == cities.index("Vilnius"), 1, 0) for i in range(days)])
    s.add(vilnius_days == 4)

    # Seville: 3 days
    seville_days = Sum([If(city_vars[i] == cities.index("Seville"), 1, 0) for i in range(days)])
    s.add(seville_days == 3)

    # Geneva: 5 days
    geneva_days = Sum([If(city_vars[i] == cities.index("Geneva"), 1, 0) for i in range(days)])
    s.add(geneva_days == 5)

    # Valencia: 5 days
    valencia_days = Sum([If(city_vars[i] == cities.index("Valencia"), 1, 0) for i in range(days)])
    s.add(valencia_days == 5)

    # Munich: 3 days, days 13-15
    for i in range(12, 15):
        s.add(city_vars[i] == cities.index("Munich"))
    munich_days = Sum([If(city_vars[i] == cities.index("Munich"), 1, 0) for i in range(days)])
    s.add(munich_days == 3)

    # Reykjavik: 4 days, days 1-4
    for i in range(0, 4):
        s.add(city_vars[i] == cities.index("Reykjavik"))
    reykjavik_days = Sum([If(city_vars[i] == cities.index("Reykjavik"), 1, 0) for i in range(days)])
    s.add(reykjavik_days == 4)

    if s.check() == sat:
        model = s.model()
        itinerary = []
        current_place = None
        start_day = 1
        for day in range(1, days + 1):
            city_idx = model.evaluate(city_vars[day - 1]).as_long()
            city = cities[city_idx]
            if day == 1:
                current_place = city
                start_day = 1
            else:
                prev_city_idx = model.evaluate(city_vars[day - 2]).as_long()
                prev_city = cities[prev_city_idx]
                if city != prev_city:
                    if start_day != day - 1:
                        itinerary.append({"day_range": f"Day {start_day}-{day - 1}", "place": prev_city})
                    else:
                        itinerary.append({"day_range": f"Day {start_day}", "place": prev_city})
                    itinerary.append({"day_range": f"Day {day}", "place": prev_city})
                    itinerary.append({"day_range": f"Day {day}", "place": city})
                    current_place = city
                    start_day = day
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