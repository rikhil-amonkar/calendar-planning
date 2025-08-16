from z3 import *
import json

def solve_itinerary():
    # Cities and indices
    cities = [
        "Barcelona",
        "Frankfurt",
        "Florence",
        "Stockholm",
        "Venice",
        "Stuttgart",
        "Salzburg",
    ]
    idx = {c: i for i, c in enumerate(cities)}

    # Direct flights (undirected)
    undirected_edges = [
        ("Barcelona", "Frankfurt"),
        ("Florence", "Frankfurt"),
        ("Stockholm", "Barcelona"),
        ("Barcelona", "Florence"),
        ("Venice", "Barcelona"),
        ("Stuttgart", "Barcelona"),
        ("Frankfurt", "Salzburg"),
        ("Stockholm", "Frankfurt"),
        ("Stuttgart", "Stockholm"),
        ("Stuttgart", "Frankfurt"),
        ("Venice", "Stuttgart"),
        ("Venice", "Frankfurt"),
    ]
    edges = set()
    for a, b in undirected_edges:
        edges.add((idx[a], idx[b]))
        edges.add((idx[b], idx[a]))

    # Desired counted days per city (including flight-day double count)
    desired = {
        "Salzburg": 4,
        "Stockholm": 2,
        "Venice": 5,
        "Frankfurt": 4,
        "Florence": 4,
        "Barcelona": 2,
        "Stuttgart": 3,
    }
    desired_by_idx = {idx[k]: v for k, v in desired.items()}

    DAYS = 18
    s = Solver()

    # Variables: place[d] = city index on day d (1-based days for readability)
    place = [Int(f"place_{d}") for d in range(1, DAYS + 1)]

    # Domains
    for d in range(DAYS):
        s.add(And(place[d] >= 0, place[d] < len(cities)))

    # Movement constraints: either stay in same city or take a direct flight
    for d in range(1, DAYS):
        same = place[d] == place[d - 1]
        allowed_flights = Or(*[And(place[d - 1] == a, place[d] == b) for (a, b) in edges]) if edges else False
        s.add(Or(same, allowed_flights))

    # Helper: inCity(c, d) is True if city c is counted on day d under the "flight day counts for both cities" rule.
    def inCity(c_idx, d):
        # d is 0-based index in code, but represents day d+1
        if d == 0:
            return place[0] == c_idx
        else:
            # Count day d for c if:
            # - You're mapped to c on day d; OR
            # - You left c on day d (i.e., day d-1 is c and day d is not c)
            return Or(place[d] == c_idx, And(place[d - 1] == c_idx, place[d] != c_idx))

    # Enforce counted days per city
    for c_idx, cnt in desired_by_idx.items():
        s.add(Sum([If(inCity(c_idx, d), 1, 0) for d in range(DAYS)]) == cnt)

    # Attend the Venice show from Day 1 to Day 5 (inclusive).
    ven = idx["Venice"]
    # Day 1 must be Venice (can't have a departure day without a previous day)
    s.add(place[0] == ven)
    # Days 2..5: must be in Venice under the counting rule
    for d in range(1, 5):  # d=1..4 correspond to Day 2..5
        s.add(inCity(ven, d))

    # The total number of transitions must be 6 since sum(desired) = 24 and horizon = 18
    # Sum over transitions (place[d] != place[d-1]) for d=2..18 equals 6
    transitions = [If(place[d] != place[d - 1], 1, 0) for d in range(1, DAYS)]
    s.add(Sum(transitions) == 6)

    if s.check() != sat:
        raise RuntimeError("No valid itinerary found under given constraints.")

    m = s.model()

    itinerary = []
    for d in range(DAYS):
        city_name = cities[m[place[d]].as_long()]
        itinerary.append({"day": d + 1, "place": city_name})

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False, indent=2))

if __name__ == "__main__":
    solve_itinerary()