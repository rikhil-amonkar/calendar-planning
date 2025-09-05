import json
from z3 import Int, Solver, And, Or, If, Distinct, Sum, sat

def main():
    # Define cities and mapping
    cities = [
        "Warsaw",
        "Porto",
        "Naples",
        "Brussels",
        "Split",
        "Reykjavik",
        "Amsterdam",
        "Lyon",
        "Helsinki",
        "Valencia",
    ]
    city_to_id = {name: i for i, name in enumerate(cities)}
    id_to_city = {i: name for i, name in enumerate(cities)}

    # Required durations (days in each city)
    durations_required = {
        city_to_id["Warsaw"]: 3,
        city_to_id["Porto"]: 5,
        city_to_id["Naples"]: 4,
        city_to_id["Brussels"]: 3,
        city_to_id["Split"]: 3,
        city_to_id["Reykjavik"]: 5,
        city_to_id["Amsterdam"]: 4,
        city_to_id["Lyon"]: 3,
        city_to_id["Helsinki"]: 4,
        city_to_id["Valencia"]: 2,
    }

    total_days = 27
    n_segments = len(cities)  # visiting all 10 cities, one contiguous segment per city

    # Windows (must be in the city for the inclusive range)
    # Interpreting "between day x and day y" inclusively
    windows = [
        (city_to_id["Porto"], 1, 5),        # workshop in Porto between day 1 and 5
        (city_to_id["Naples"], 17, 20),     # conference in Naples between day 17 and 20
        (city_to_id["Brussels"], 20, 22),   # show in Brussels from day 20 to day 22
        (city_to_id["Amsterdam"], 5, 8),    # visit relatives in Amsterdam between day 5 and 8
        (city_to_id["Helsinki"], 8, 11),    # wedding in Helsinki between day 8 and 11
    ]

    # Direct flights (undirected)
    flights_list = [
        ("Amsterdam", "Warsaw"),
        ("Helsinki", "Brussels"),
        ("Helsinki", "Warsaw"),
        ("Reykjavik", "Brussels"),
        ("Amsterdam", "Lyon"),
        ("Amsterdam", "Naples"),
        ("Amsterdam", "Reykjavik"),
        ("Naples", "Valencia"),
        ("Porto", "Brussels"),
        ("Amsterdam", "Split"),
        ("Lyon", "Split"),
        ("Warsaw", "Split"),
        ("Porto", "Amsterdam"),
        ("Helsinki", "Split"),
        ("Brussels", "Lyon"),
        ("Porto", "Lyon"),
        ("Reykjavik", "Warsaw"),
        ("Brussels", "Valencia"),
        ("Valencia", "Lyon"),
        ("Porto", "Warsaw"),
        ("Warsaw", "Valencia"),
        ("Amsterdam", "Helsinki"),
        ("Porto", "Valencia"),
        ("Warsaw", "Brussels"),
        ("Warsaw", "Naples"),
        ("Naples", "Split"),
        ("Helsinki", "Naples"),
        ("Helsinki", "Reykjavik"),
        ("Amsterdam", "Valencia"),
        ("Naples", "Brussels"),
    ]
    # Build adjacency as bidirectional set of (idA, idB)
    adj_pairs = set()
    for a, b in flights_list:
        ai = city_to_id[a]
        bi = city_to_id[b]
        adj_pairs.add((ai, bi))
        adj_pairs.add((bi, ai))

    # Z3 Variables
    city_vars = [Int(f"city_{i}") for i in range(n_segments)]
    start_vars = [Int(f"start_{i}") for i in range(n_segments)]
    end_vars = [Int(f"end_{i}") for i in range(n_segments)]

    s = Solver()

    # Domains and structure constraints
    for i in range(n_segments):
        s.add(city_vars[i] >= 0, city_vars[i] < len(cities))
        s.add(start_vars[i] >= 1, start_vars[i] <= total_days)
        s.add(end_vars[i] >= 1, end_vars[i] <= total_days)
        s.add(start_vars[i] <= end_vars[i])

    # Use each city exactly once
    s.add(Distinct(city_vars))

    # Day chain: segments overlap one day at boundaries to model flight day counts for both cities
    s.add(start_vars[0] == 1)
    s.add(end_vars[-1] == total_days)
    for i in range(n_segments - 1):
        s.add(start_vars[i + 1] == end_vars[i])  # travel on this day counts for both cities

    # Adjacency constraints: consecutive cities must have a direct flight
    for i in range(n_segments - 1):
        allowed = []
        for (a, b) in adj_pairs:
            allowed.append(And(city_vars[i] == a, city_vars[i + 1] == b))
        s.add(Or(*allowed))

    # Duration per city
    durations_expr = [end_vars[i] - start_vars[i] + 1 for i in range(n_segments)]
    for cid, req_days in durations_required.items():
        s.add(Sum([If(city_vars[i] == cid, durations_expr[i], 0) for i in range(n_segments)]) == req_days)

    # Window constraints: city must cover the entire window (inclusive)
    for cid, w_start, w_end in windows:
        s.add(Or(*[
            And(city_vars[i] == cid, start_vars[i] <= w_start, end_vars[i] >= w_end)
            for i in range(n_segments)
        ]))

    # Solve
    if s.check() != sat:
        print(json.dumps({"error": "No feasible itinerary found."}))
        return

    m = s.model()
    segments = []
    for i in range(n_segments):
        city_id = m[city_vars[i]].as_long()
        start_day = m[start_vars[i]].as_long()
        end_day = m[end_vars[i]].as_long()
        segments.append((start_day, end_day, id_to_city[city_id]))

    # Sort by start day (should already be in order)
    segments.sort(key=lambda x: x[0])

    itinerary = []
    for start_day, end_day, city_name in segments:
        itinerary.append({
            "day_range": f"Day {start_day}-{end_day}",
            "place": city_name
        })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()