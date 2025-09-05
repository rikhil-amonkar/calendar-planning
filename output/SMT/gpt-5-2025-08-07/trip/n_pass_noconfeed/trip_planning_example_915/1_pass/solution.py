import json
from z3 import *

def main():
    # Cities
    cities = [
        "Bucharest", "Venice", "Prague", "Frankfurt",
        "Zurich", "Florence", "Tallinn"
    ]
    BUCHAREST, VENICE, PRAGUE, FRANKFURT, ZURICH, FLORENCE, TALLINN = range(7)

    # Required total days per city (including arrival-flight overlap counting)
    required_days = {
        BUCHAREST: 3,
        VENICE: 5,
        PRAGUE: 4,
        FRANKFURT: 5,
        ZURICH: 5,
        FLORENCE: 5,
        TALLINN: 5,
    }

    # Allowed directed flights (i -> j). "and" => bidirectional; explicit one-way noted
    directed_edges = set()

    def add_bidirectional(a, b):
        directed_edges.add((a, b))
        directed_edges.add((b, a))

    # From the problem statement:
    add_bidirectional(PRAGUE, TALLINN)
    add_bidirectional(PRAGUE, ZURICH)
    add_bidirectional(FLORENCE, PRAGUE)
    add_bidirectional(FRANKFURT, BUCHAREST)
    add_bidirectional(FRANKFURT, VENICE)
    add_bidirectional(PRAGUE, BUCHAREST)
    add_bidirectional(BUCHAREST, ZURICH)
    add_bidirectional(TALLINN, FRANKFURT)
    directed_edges.add((ZURICH, FLORENCE))  # one-way
    add_bidirectional(FRANKFURT, ZURICH)
    add_bidirectional(ZURICH, VENICE)
    add_bidirectional(FLORENCE, FRANKFURT)
    add_bidirectional(PRAGUE, FRANKFURT)
    add_bidirectional(TALLINN, ZURICH)

    days = 26
    solver = Solver()

    # Day -> assigned city variable
    city = [Int(f"city_{d+1}") for d in range(days)]
    for d in range(days):
        solver.add(And(city[d] >= 0, city[d] < len(cities)))

    # Direct flight constraint between consecutive different cities
    for d in range(days - 1):
        # Either stay in same city or must be an allowed directed flight
        conds = [city[d] == city[d+1]]
        for (i, j) in directed_edges:
            conds.append(And(city[d] == i, city[d+1] == j))
        solver.add(Or(*conds))

    # Presence boolean: presence[c][d] = in city c on day d (either assigned that day, or arrived via flight on day d)
    presence = {c: [Bool(f"present_{cities[c]}_{d+1}") for d in range(days)] for c in range(len(cities))}

    for c in range(len(cities)):
        for d in range(days):
            if d < days - 1:
                # present if assigned that day OR if day d is a flight day arriving into c (i.e., city[d+1] == c and city[d] != city[d+1])
                solver.add(presence[c][d] == Or(city[d] == c, And(city[d] != city[d+1], city[d+1] == c)))
            else:
                # last day: only assigned counts (no arrival on day 26)
                solver.add(presence[c][d] == (city[d] == c))

    # Exact day totals per city
    for c, req in required_days.items():
        solver.add(Sum([If(presence[c][d], 1, 0) for d in range(days)]) == req)

    # "At least one day in window" constraints for events
    # - Wedding in Venice between day 22 and 26 (inclusive)
    solver.add(Or([presence[VENICE][d-1] for d in range(22, 27)]))
    # - Show in Frankfurt between day 12 and 16 (inclusive)
    solver.add(Or([presence[FRANKFURT][d-1] for d in range(12, 17)]))
    # - Meet friends in Tallinn between day 8 and 12 (inclusive)
    solver.add(Or([presence[TALLINN][d-1] for d in range(8, 13)]))

    # Solve
    if solver.check() != sat:
        print(json.dumps({"error": "No feasible itinerary found with given constraints."}))
        return

    m = solver.model()
    assigned = [m.evaluate(city[d]).as_long() for d in range(days)]

    # Build contiguous day ranges by assigned city
    itinerary = []
    start = 1
    current_city = assigned[0]
    for d in range(2, days + 1):
        if assigned[d - 1] != current_city:
            itinerary.append({
                "day_range": f"Day {start}-{d-1}",
                "place": cities[current_city]
            })
            start = d
            current_city = assigned[d - 1]
    # Last block
    itinerary.append({
        "day_range": f"Day {start}-{days}",
        "place": cities[current_city]
    })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()