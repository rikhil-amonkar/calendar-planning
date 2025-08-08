import json
from z3 import *

def solve_itinerary():
    # Define cities and required days
    cities = {
        "Lyon": 3,
        "Paris": 5,
        "Riga": 2,
        "Berlin": 2,
        "Stockholm": 3,
        "Zurich": 5,
        "Nice": 2,
        "Seville": 3,
        "Milan": 3,
        "Naples": 4
    }

    # Corrected and verified direct flights (bidirectional)
    direct_flights = [
        ("Paris", "Stockholm"),
        ("Seville", "Paris"),
        ("Naples", "Zurich"),
        ("Nice", "Riga"),
        ("Berlin", "Milan"),
        ("Paris", "Zurich"),
        ("Paris", "Nice"),
        ("Milan", "Paris"),
        ("Milan", "Riga"),
        ("Paris", "Lyon"),
        ("Milan", "Naples"),
        ("Paris", "Riga"),
        ("Berlin", "Stockholm"),
        ("Stockholm", "Riga"),
        ("Nice", "Zurich"),
        ("Milan", "Zurich"),
        ("Lyon", "Nice"),
        ("Zurich", "Stockholm"),
        ("Zurich", "Riga"),
        ("Berlin", "Naples"),
        ("Milan", "Stockholm"),
        ("Berlin", "Zurich"),
        ("Milan", "Seville"),
        ("Paris", "Naples"),
        ("Berlin", "Riga"),
        ("Nice", "Stockholm"),
        ("Berlin", "Paris"),
        ("Nice", "Naples"),
        ("Berlin", "Nice")
    ]

    # Standardize city names and make flights bidirectional
    corrected_flights = set()
    for a, b in direct_flights:
        a = a.replace("Zurich", "Zurich").replace("Stockholm", "Stockholm").replace("Milan", "Milan")
        b = b.replace("Zurich", "Zurich").replace("Stockholm", "Stockholm").replace("Milan", "Milan")
        corrected_flights.add((a, b))
        corrected_flights.add((b, a))

    # Create city list and day count
    city_names = sorted(cities.keys())
    n_days = 23

    # Initialize solver
    s = Solver()

    # Create day variables (0-indexed cities)
    day_vars = [Int(f"day_{i}") for i in range(n_days)]
    for day in day_vars:
        s.add(day >= 0, day < len(city_names))

    # Helper function
    def city_idx(city):
        return city_names.index(city)

    # Duration constraints
    for city, days in cities.items():
        idx = city_idx(city)
        s.add(Sum([If(day_vars[i] == idx, 1, 0) for i in range(n_days)]) == days)

    # Flight constraints - consecutive days must be same city or connected
    for i in range(n_days - 1):
        current = day_vars[i]
        next_day = day_vars[i + 1]
        same_city = current == next_day
        flight_options = []
        for a, b in corrected_flights:
            a_idx = city_idx(a)
            b_idx = city_idx(b)
            flight_options.append(And(current == a_idx, next_day == b_idx))
        s.add(Or(same_city, Or(flight_options)))

    # Event constraints
    # Wedding in Berlin on days 1-2 (must be consecutive)
    s.add(day_vars[0] == city_idx("Berlin"))
    s.add(day_vars[1] == city_idx("Berlin"))

    # Workshop in Nice on day 12 or 13 (must be one of these days)
    s.add(Or(day_vars[11] == city_idx("Nice"), day_vars[12] == city_idx("Nice")))

    # Annual show in Stockholm on days 20-22 (must be consecutive)
    s.add(day_vars[19] == city_idx("Stockholm"))
    s.add(day_vars[20] == city_idx("Stockholm"))
    s.add(day_vars[21] == city_idx("Stockholm"))

    # Additional constraints to help the solver
    # Ensure we don't have impossible single-day visits between events
    for i in range(2, 11):  # Days between Berlin wedding and Nice workshop
        s.add(day_vars[i] != city_idx("Nice"))
    for i in range(13, 19):  # Days between Nice workshop and Stockholm show
        s.add(day_vars[i] != city_idx("Stockholm"))

    # Try to solve
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(n_days):
            city_idx = model.evaluate(day_vars[i]).as_long()
            itinerary.append({"day": i + 1, "place": city_names[city_idx]})
        
        # Verify all constraints are met
        if verify_itinerary(itinerary, cities, corrected_flights):
            return {"itinerary": itinerary}
        else:
            return {"error": "Generated itinerary failed verification"}
    else:
        return {"error": "No valid itinerary found"}

def verify_itinerary(itinerary, cities, corrected_flights):
    # Verify day counts
    day_counts = {city: 0 for city in cities}
    for day in itinerary:
        day_counts[day["place"]] += 1
    for city, count in day_counts.items():
        if count != cities[city]:
            return False

    # Verify flight connections
    for i in range(len(itinerary) - 1):
        current = itinerary[i]["place"]
        next_place = itinerary[i + 1]["place"]
        if current != next_place and (current, next_place) not in corrected_flights:
            return False

    # Verify event constraints
    if itinerary[0]["place"] != "Berlin" or itinerary[1]["place"] != "Berlin":
        return False
    if not (itinerary[11]["place"] == "Nice" or itinerary[12]["place"] == "Nice"):
        return False
    if not (itinerary[19]["place"] == "Stockholm" and 
            itinerary[20]["place"] == "Stockholm" and 
            itinerary[21]["place"] == "Stockholm"):
        return False

    return True

# Run and print result
result = solve_itinerary()
print(json.dumps(result, indent=2))