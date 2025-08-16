# Requires: z3-solver
# pip install z3-solver

from z3 import *
import json

def solve_itinerary():
    # Define cities and mapping
    cities = [
        "Venice", "Nice", "Naples", "Amsterdam", "Valencia",
        "Stuttgart", "Split", "Barcelona", "Porto"
    ]
    idx = {name: i for i, name in enumerate(cities)}
    n_days = 24

    # Required total "counted" days per city (including flight-day double counts)
    required_days = {
        "Naples": 3,
        "Valencia": 5,
        "Stuttgart": 2,
        "Split": 5,
        "Venice": 5,
        "Amsterdam": 4,
        "Nice": 2,
        "Barcelona": 2,
        "Porto": 4,
    }

    # Direct flight edges (undirected)
    edges = [
        ("Venice", "Nice"),
        ("Naples", "Amsterdam"),
        ("Barcelona", "Nice"),
        ("Amsterdam", "Nice"),
        ("Stuttgart", "Valencia"),
        ("Stuttgart", "Porto"),
        ("Split", "Stuttgart"),
        ("Split", "Naples"),
        ("Valencia", "Amsterdam"),
        ("Barcelona", "Porto"),
        ("Valencia", "Naples"),
        ("Venice", "Amsterdam"),
        ("Barcelona", "Naples"),
        ("Barcelona", "Valencia"),
        ("Split", "Amsterdam"),
        ("Barcelona", "Venice"),
        ("Stuttgart", "Amsterdam"),
        ("Naples", "Nice"),
        ("Venice", "Stuttgart"),
        ("Split", "Barcelona"),
        ("Porto", "Nice"),
        ("Barcelona", "Stuttgart"),
        ("Venice", "Naples"),
        ("Porto", "Amsterdam"),
        ("Porto", "Valencia"),
        ("Stuttgart", "Naples"),
        ("Barcelona", "Amsterdam"),
    ]
    # Build allowed pairs (both directions)
    allowed_pairs = set()
    for a, b in edges:
        ai, bi = idx[a], idx[b]
        allowed_pairs.add((ai, bi))
        allowed_pairs.add((bi, ai))
    # Same-city (no flight) always allowed
    for i in range(len(cities)):
        allowed_pairs.add((i, i))

    # Z3 variables: city per day (0-based days 0..23)
    city = [Int(f"day_{d+1}") for d in range(n_days)]

    s = Solver()

    # Domain constraints
    for d in range(n_days):
        s.add(And(city[d] >= 0, city[d] < len(cities)))

    # Direct flight constraints between consecutive different cities
    for d in range(n_days - 1):
        # Or the pair is in allowed_pairs
        disj = []
        for (a, b) in allowed_pairs:
            disj.append(And(city[d] == a, city[d+1] == b))
        s.add(Or(*disj))

    # Helper to build InCityDay predicate (0-based day index)
    def in_city_day(c_idx, day_idx):
        # In city if assigned that day OR arrival to that city occurs on that day
        assigned = (city[day_idx] == c_idx)
        arrival = False
        if day_idx < n_days - 1:
            arrival = And(city[day_idx] != city[day_idx + 1], city[day_idx + 1] == c_idx)
        else:
            arrival = False
        return Or(assigned, arrival)

    # Duration (counted days) per city: assigned days + arrival days
    for name, req in required_days.items():
        c = idx[name]
        assigned_sum = Sum([If(city[d] == c, 1, 0) for d in range(n_days)])
        arrival_sum = Sum([If(And(city[d] != city[d+1], city[d+1] == c), 1, 0) for d in range(n_days - 1)])
        s.add(assigned_sum + arrival_sum == req)

    # Conference in Venice on day 6 and day 10 (1-based days -> 0-based indices 5 and 9)
    s.add(in_city_day(idx["Venice"], 5))   # Day 6
    s.add(in_city_day(idx["Venice"], 9))   # Day 10

    # Workshop in Barcelona between day 5 and day 6: be in Barcelona on day 5 or day 6
    s.add(Or(in_city_day(idx["Barcelona"], 4), in_city_day(idx["Barcelona"], 5)))  # Days 5 or 6

    # Meet friend in Naples between day 18 and 20 (inclusive)
    s.add(Or(in_city_day(idx["Naples"], 17), in_city_day(idx["Naples"], 18), in_city_day(idx["Naples"], 19)))

    # Meet friends in Nice between day 23 and 24 (inclusive)
    s.add(Or(in_city_day(idx["Nice"], 22), in_city_day(idx["Nice"], 23)))

    # Optional: enforce exact number of flights equals sum(required) - total_days
    total_required = sum(required_days.values())
    flights = Sum([If(city[d] != city[d+1], 1, 0) for d in range(n_days - 1)])
    s.add(flights == total_required - n_days)  # 32 - 24 = 8 flights

    # Solve
    if s.check() != sat:
        raise RuntimeError("No feasible itinerary found under given constraints.")

    m = s.model()
    itinerary = []
    for d in range(n_days):
        city_name = cities[m[city[d]].as_long()]
        itinerary.append({"day": d + 1, "city": city_name})

    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    solve_itinerary()