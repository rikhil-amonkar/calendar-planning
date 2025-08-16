from z3 import *
import json

def solve_itinerary():
    # Define cities and indices
    cities = [
        "Venice", "Reykjavik", "Munich", "Santorini", "Manchester",
        "Porto", "Bucharest", "Tallinn", "Valencia", "Vienna"
    ]
    idx = {c: i for i, c in enumerate(cities)}

    # Required total counted days per city (including flight-day double counting)
    required_days = {
        "Venice": 3,
        "Reykjavik": 2,
        "Munich": 3,
        "Santorini": 3,
        "Manchester": 3,
        "Porto": 3,
        "Bucharest": 5,
        "Tallinn": 4,
        "Valencia": 2,
        "Vienna": 5
    }

    # Direct flights (undirected)
    edge_list = [
        ("Bucharest", "Manchester"),
        ("Munich", "Venice"),
        ("Santorini", "Manchester"),
        ("Vienna", "Reykjavik"),
        ("Venice", "Santorini"),
        ("Munich", "Porto"),
        ("Valencia", "Vienna"),
        ("Manchester", "Vienna"),
        ("Porto", "Vienna"),
        ("Venice", "Manchester"),
        ("Santorini", "Vienna"),
        ("Munich", "Manchester"),
        ("Munich", "Reykjavik"),
        ("Bucharest", "Valencia"),
        ("Venice", "Vienna"),
        ("Bucharest", "Vienna"),
        ("Porto", "Manchester"),
        ("Munich", "Vienna"),
        ("Valencia", "Porto"),
        ("Munich", "Bucharest"),
        ("Tallinn", "Munich"),
        ("Santorini", "Bucharest"),
        ("Munich", "Valencia")
    ]
    edges = set()
    for a, b in edge_list:
        edges.add((idx[a], idx[b]))
        edges.add((idx[b], idx[a]))

    # Z3 variables: city per day (1..24)
    D = 24
    City = [Int(f"City_{d}") for d in range(1, D + 1)]

    s = Solver()

    # Domain constraints
    for d in range(D):
        s.add(And(City[d] >= 0, City[d] < len(cities)))

    # Direct flight constraints: if change day-to-day, must be along an allowed edge
    for d in range(1, D):  # compare day d and day d-1 (0-indexed)
        prev_c = City[d - 1]
        curr_c = City[d]
        allowed_move = Or(prev_c == curr_c,
                          Or([And(prev_c == a, curr_c == b) for (a, b) in edges]))
        s.add(allowed_move)

    # Counted days per city with flight-day double count:
    # For each city i:
    # count_i = sum_{day=1..24} [City(day)==i] + sum_{day=2..24} [City(day-1)==i and City(day)!=City(day-1)]
    counts = {}
    for i in range(len(cities)):
        stay_part = [If(City[d] == i, 1, 0) for d in range(D)]
        depart_part = [
            If(And(City[d - 1] == i, City[d - 1] != City[d]), 1, 0)
            for d in range(1, D)
        ]
        count_i = Sum(*(stay_part + depart_part))
        counts[i] = count_i
        s.add(count_i == required_days[cities[i]])

    # Total transitions equals 9 (since sum(required) - 24 = 9)
    transitions = Sum(*[If(City[d] != City[d - 1], 1, 0) for d in range(1, D)])
    s.add(transitions == (sum(required_days.values()) - D))

    # Special day membership constraints (day numbers are 1-based):
    # Days 4-6 must count towards Munich
    for d in range(4, 7):
        if d == 1:
            s.add(City[d - 1] == idx["Munich"])
        else:
            s.add(Or(
                City[d - 1] == idx["Munich"],  # being in Munich on day d
                And(City[d - 2] == idx["Munich"], City[d - 2] != City[d - 1])  # departed Munich on day d
            ))

    # Days 8-10 must count towards Santorini
    for d in range(8, 11):
        s.add(Or(
            City[d - 1] == idx["Santorini"],
            And(City[d - 2] == idx["Santorini"], City[d - 2] != City[d - 1])
        ))

    # Days 14-15 must count towards Valencia
    for d in range(14, 16):
        s.add(Or(
            City[d - 1] == idx["Valencia"],
            And(City[d - 2] == idx["Valencia"], City[d - 2] != City[d - 1])
        ))

    # Solve
    if s.check() != sat:
        raise RuntimeError("No feasible itinerary found given the constraints.")

    m = s.model()

    # Build the JSON itinerary (day -> city name)
    itinerary = []
    for d in range(D):
        city_idx = m.evaluate(City[d]).as_long()
        itinerary.append({"day": d + 1, "city": cities[city_idx]})

    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = solve_itinerary()
    print(json.dumps(result, ensure_ascii=False, indent=2))