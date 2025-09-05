import json
from z3 import *

def main():
    # Parameters
    total_days = 19
    cities = ["Dubrovnik", "Warsaw", "Stuttgart", "Bucharest", "Copenhagen"]
    city_index = {name: i for i, name in enumerate(cities)}
    num_cities = len(cities)

    # Required presence (days credited in each city, counting flight-day overlap)
    required_days = {
        "Dubrovnik": 5,
        "Warsaw": 2,
        "Stuttgart": 7,
        "Bucharest": 6,
        "Copenhagen": 3
    }

    # Direct flights (undirected)
    direct_pairs = [
        ("Warsaw", "Copenhagen"),
        ("Stuttgart", "Copenhagen"),
        ("Warsaw", "Stuttgart"),
        ("Bucharest", "Copenhagen"),
        ("Bucharest", "Warsaw"),
        ("Copenhagen", "Dubrovnik"),
    ]
    edges = set()
    for a, b in direct_pairs:
        ai, bi = city_index[a], city_index[b]
        edges.add((ai, bi))
        edges.add((bi, ai))

    # Z3 variables
    N = total_days
    EndCity = [Int(f"city_{d+1}") for d in range(N)]  # End-of-day city for each day
    Flight = [Bool(f"flight_{d+1}") for d in range(N)]  # Whether a flight occurs on day d (day 1 has no previous -> no flight)
    Present = [[Bool(f"present_{cities[c]}_day_{d+1}") for d in range(N)] for c in range(num_cities)]

    s = Solver()

    # Domain constraints for cities
    for d in range(N):
        s.add(And(EndCity[d] >= 0, EndCity[d] < num_cities))

    # Flight definition and direct flight constraints
    s.add(Flight[0] == False)  # No flight on day 1 (no previous day)
    for d in range(1, N):
        s.add(Flight[d] == (EndCity[d] != EndCity[d-1]))
        # If a flight happens on day d+1, it must be on a direct route
        edge_constraints = []
        for (i, j) in edges:
            edge_constraints.append(And(EndCity[d-1] == i, EndCity[d] == j))
        s.add(Implies(Flight[d], Or(edge_constraints)))

    # Presence definition:
    # On day d, you are present in EndCity[d], and if a flight occurs that day (d>0),
    # you are also present in the previous day's city.
    for c in range(num_cities):
        for d in range(N):
            if d == 0:
                s.add(Present[c][d] == (EndCity[d] == c))
            else:
                s.add(Present[c][d] == Or(EndCity[d] == c, And(Flight[d], EndCity[d-1] == c)))

    # Required presence counts per city
    for name, req in required_days.items():
        c = city_index[name]
        s.add(Sum([If(Present[c][d], 1, 0) for d in range(N)]) == req)

    # The sum of flights must account for overlap: Sum(required_days) - total_days
    total_presence = sum(required_days.values())
    required_flights = total_presence - total_days
    s.add(Sum([If(Flight[d], 1, 0) for d in range(1, N)]) == required_flights)

    # Conference constraints: Day 7 and Day 13 must include Stuttgart
    stuttgart = city_index["Stuttgart"]
    s.add(Present[stuttgart][6] == True)   # Day 7 (index 6)
    s.add(Present[stuttgart][12] == True)  # Day 13 (index 12)

    # Wedding in Bucharest between day 1 and day 6 inclusive
    bucharest = city_index["Bucharest"]
    s.add(Or([Present[bucharest][d] for d in range(0, 6)]))

    # Solve
    if s.check() != sat:
        raise RuntimeError("No feasible itinerary found with given constraints.")

    m = s.model()

    # Extract end-of-day cities
    end_cities = [m.evaluate(EndCity[d]).as_long() for d in range(N)]

    # Build compressed itinerary segments by consecutive same end city
    itinerary = []
    start_day = 1
    current_city = end_cities[0]
    for d in range(1, N):
        if end_cities[d] != current_city:
            itinerary.append({
                "day_range": f"Day {start_day}-{d}",
                "place": cities[current_city]
            })
            start_day = d + 1
            current_city = end_cities[d]
    # Append last segment
    itinerary.append({
        "day_range": f"Day {start_day}-{N}",
        "place": cities[current_city]
    })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()