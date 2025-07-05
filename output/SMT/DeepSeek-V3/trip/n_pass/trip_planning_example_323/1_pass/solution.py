from z3 import *

def solve_itinerary():
    # Cities
    cities = ["London", "Oslo", "Split", "Porto"]
    city_map = {c: i for i, c in enumerate(cities)}
    n_days = 16

    # Initialize Z3 solver
    s = Solver()

    # Variables: day i is in city (represented as integers)
    day_city = [Int(f"day_{i}_city") for i in range(1, n_days + 1)]
    for dc in day_city:
        s.add(And(dc >= 0, dc < len(cities)))

    # Flight transitions: possible direct flights
    direct_flights = [
        (city_map["London"], city_map["Oslo"]),
        (city_map["Oslo"], city_map["London"]),
        (city_map["Split"], city_map["Oslo"]),
        (city_map["Oslo"], city_map["Split"]),
        (city_map["Oslo"], city_map["Porto"]),
        (city_map["Porto"], city_map["Oslo"]),
        (city_map["London"], city_map["Split"]),
        (city_map["Split"], city_map["London"])
    ]

    # Constraints for valid transitions between consecutive days
    for i in range(n_days - 1):
        current_city = day_city[i]
        next_city = day_city[i+1]
        # Either stay in the same city or take a direct flight
        s.add(Or(
            current_city == next_city,
            Or([And(current_city == a, next_city == b) for (a, b) in direct_flights])
        ))

    # Constraints for total days in each city
    total_days = {city: 0 for city in cities}
    for city_idx, city in enumerate(cities):
        total = 0
        for day in range(n_days):
            total += If(day_city[day] == city_idx, 1, 0)
        total_days[city] = total

    # Specific constraints
    # Split: 5 days, including days 7-11
    s.add(total_days["Split"] == 5)
    for day in range(7 - 1, 11):  # days 7 to 11 (1-based to 0-based)
        s.add(day_city[day] == city_map["Split"])

    # Oslo: 2 days
    s.add(total_days["Oslo"] == 2)

    # London: 7 days, with relatives between day 1 and 7 (i.e., days 1-7 in 1-based)
    s.add(total_days["London"] == 7)
    for day in range(1 - 1, 7):  # days 1 to 7 (0-based)
        s.add(day_city[day] == city_map["London"])

    # Porto: 5 days
    s.add(total_days["Porto"] == 5)

    # Check and get model
    if s.check() == sat:
        model = s.model()
        itinerary = []
        current_place = None
        start_day = 1

        # Helper to add entries
        def add_entry(s_day, e_day, place):
            if s_day == e_day:
                itinerary.append({"day_range": f"Day {s_day}", "place": place})
            else:
                itinerary.append({"day_range": f"Day {s_day}-{e_day}", "place": place})

        # Generate itinerary
        for day in range(1, n_days + 1):
            city_idx = model.evaluate(day_city[day - 1]).as_long()
            place = cities[city_idx]
            if day == 1:
                current_place = place
                start_day = 1
            else:
                prev_city_idx = model.evaluate(day_city[day - 2]).as_long()
                prev_place = cities[prev_city_idx]
                if prev_place != place:
                    # Flight day: add previous place up to day-1, then add flight day for both
                    add_entry(start_day, day - 1, prev_place)
                    itinerary.append({"day_range": f"Day {day - 1}", "place": prev_place})
                    itinerary.append({"day_range": f"Day {day - 1}", "place": place})
                    start_day = day
                    current_place = place
        # Add the last segment
        add_entry(start_day, n_days, current_place)

        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Generate and print the itinerary
itinerary = solve_itinerary()
import json
print(json.dumps(itinerary, indent=2))