import json
from z3 import *

def solve_itinerary():
    # Cities and durations (days in each city)
    cities = ["Helsinki", "Reykjavik", "Budapest", "Warsaw", "Madrid", "Split"]
    city_idx = {name: i for i, name in enumerate(cities)}
    durations = {
        city_idx["Helsinki"]: 2,
        city_idx["Reykjavik"]: 2,
        city_idx["Warsaw"]: 3,
        city_idx["Madrid"]: 4,
        city_idx["Split"]: 4,
        city_idx["Budapest"]: 4,
    }

    # Directed flight edges
    symmetric_pairs = [
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
    ]
    directed_only = [
        ("Reykjavik", "Madrid"),
    ]
    allowed_edges = set()
    for a, b in symmetric_pairs:
        allowed_edges.add((city_idx[a], city_idx[b]))
        allowed_edges.add((city_idx[b], city_idx[a]))
    for a, b in directed_only:
        allowed_edges.add((city_idx[a], city_idx[b]))

    # Planning horizon and segments
    total_days = 14
    segments = 6  # exactly 6 cities

    # Z3 variables
    City = [Int(f"City_{i}") for i in range(segments)]
    Entry = [Int(f"Entry_{i}") for i in range(segments)]
    Exit = [Int(f"Exit_{i}") for i in range(segments)]

    s = Solver()

    # Domain constraints for city variables
    for i in range(segments):
        s.add(And(City[i] >= 0, City[i] < len(cities)))

    # All cities distinct (visit each city exactly once)
    s.add(Distinct(City))

    # Entry/Exit chaining and duration constraints
    s.add(Entry[0] == 1)
    for i in range(segments):
        # exit = entry + duration(city) - 1
        dur_expr = Sum([If(City[i] == c, durations[c], 0) for c in durations])
        s.add(Exit[i] == Entry[i] + dur_expr - 1)
        # Valid day ranges
        s.add(And(Entry[i] >= 1, Exit[i] <= total_days))
        if i < segments - 1:
            # Flight day overlap: entry of next is same as exit of current
            s.add(Entry[i + 1] == Exit[i])

    # End on day 14
    s.add(Exit[-1] == total_days)

    # Direct flight constraints between consecutive cities
    for i in range(segments - 1):
        s.add(Or([And(City[i] == a, City[i + 1] == b) for (a, b) in allowed_edges]))

    # Specific constraints:
    # - Helsinki for 2 days, workshop between day 1 and day 2 => start in Helsinki on days 1-2
    s.add(City[0] == city_idx["Helsinki"])  # First segment is Helsinki
    # Duration constraint already enforces Exit[0] = 2

    # - Reykjavik for 2 days, meet between day 8 and day 9 => Reykjavik spans days 8-9
    s.add(Or([And(City[i] == city_idx["Reykjavik"], Entry[i] == 8) for i in range(segments)]))

    # - Warsaw for 3 days, visit relatives between day 9 and day 11 => Warsaw spans days 9-11
    s.add(Or([And(City[i] == city_idx["Warsaw"], Entry[i] == 9) for i in range(segments)]))

    # Solve
    if s.check() != sat:
        return {"itinerary": []}

    m = s.model()

    # Extract solution
    sol = []
    for i in range(segments):
        city_name = cities[m[City[i]].as_long()]
        entry_day = m[Entry[i]].as_long()
        exit_day = m[Exit[i]].as_long()
        sol.append({"day_range": f"Day {entry_day}-{exit_day}", "place": city_name})

    return {"itinerary": sol}

if __name__ == "__main__":
    result = solve_itinerary()
    print(json.dumps(result, ensure_ascii=False))