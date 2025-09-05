import json
from z3 import *

def main():
    # Days are 1..28, but we use 0-based indices in arrays for end-of-day cities:
    N_DAYS = 28

    # Define the 10 cities (fixed set as per problem)
    cities = [
        "Prague",
        "Tallinn",
        "Warsaw",
        "Porto",
        "Naples",
        "Milan",
        "Lisbon",
        "Santorini",
        "Riga",
        "Stockholm",
    ]
    idx = {c: i for i, c in enumerate(cities)}

    # Required total "presence" durations for each city
    required_days = {
        "Prague": 5,
        "Tallinn": 3,      # must be present exactly on days 18-20
        "Warsaw": 2,
        "Porto": 3,
        "Naples": 5,
        "Milan": 3,        # must be present exactly on days 24-26
        "Lisbon": 5,
        "Santorini": 5,
        "Riga": 4,         # must be present exactly on days 5-8
        "Stockholm": 2,
    }

    # Build directed adjacency based on given direct flights list
    directed_edges = set()

    def add_bidirectional(a, b):
        directed_edges.add((idx[a], idx[b]))
        directed_edges.add((idx[b], idx[a]))

    def add_directed(a, b):
        directed_edges.add((idx[a], idx[b]))

    # Provided connections
    add_bidirectional("Riga", "Prague")
    add_bidirectional("Stockholm", "Milan")
    add_bidirectional("Riga", "Milan")
    add_bidirectional("Lisbon", "Stockholm")
    add_directed("Stockholm", "Santorini")
    add_bidirectional("Naples", "Warsaw")
    add_bidirectional("Lisbon", "Warsaw")
    add_bidirectional("Naples", "Milan")
    add_bidirectional("Lisbon", "Naples")
    add_directed("Riga", "Tallinn")
    add_bidirectional("Tallinn", "Prague")
    add_bidirectional("Stockholm", "Warsaw")
    add_bidirectional("Riga", "Warsaw")
    add_bidirectional("Lisbon", "Riga")
    add_bidirectional("Riga", "Stockholm")
    add_bidirectional("Lisbon", "Porto")
    add_bidirectional("Lisbon", "Prague")
    add_bidirectional("Milan", "Porto")
    add_bidirectional("Prague", "Milan")
    add_bidirectional("Lisbon", "Milan")
    add_bidirectional("Warsaw", "Porto")
    add_bidirectional("Warsaw", "Tallinn")
    add_bidirectional("Santorini", "Milan")
    add_bidirectional("Stockholm", "Prague")
    add_bidirectional("Stockholm", "Tallinn")
    add_bidirectional("Warsaw", "Milan")
    add_bidirectional("Santorini", "Naples")
    add_bidirectional("Warsaw", "Prague")

    # Z3 variables: end_of_day[d] is the city index where we end day d+1
    end_of_day = [Int(f"end_{d+1}") for d in range(N_DAYS)]

    s = Optimize()

    # Domains: each day end city is one of our 10 cities
    for d in range(N_DAYS):
        s.add(And(end_of_day[d] >= 0, end_of_day[d] < len(cities)))

    # Helper: presence of city c on day d (0-based index; maps to Day d+1)
    def present_expr(city_idx, d):
        if d == 0:
            return end_of_day[0] == city_idx
        else:
            return Or(end_of_day[d] == city_idx, end_of_day[d-1] == city_idx)

    # Change/flight day definition for days 2..28 (indices 1..27):
    change = [Bool(f"change_{d+1}") for d in range(N_DAYS)]
    for d in range(N_DAYS):
        if d == 0:
            s.add(change[d] == False)  # no previous day -> no change
        else:
            s.add(change[d] == (end_of_day[d] != end_of_day[d-1]))
            # If a change occurs on day d+1, it must be a direct flight:
            # Either no change OR (end[d-1], end[d]) is in directed_edges
            allowed_pairs = []
            for (a, b) in directed_edges:
                allowed_pairs.append(And(end_of_day[d-1] == a, end_of_day[d] == b))
            s.add(Or(end_of_day[d] == end_of_day[d-1], Or(*allowed_pairs)))

    # We know total presence sum across all cities equals 28 + number_of_changes (days 2..28)
    # Required sum of city presence is 37, thus total changes must be 9.
    s.add(Sum([If(change[d], 1, 0) for d in range(1, N_DAYS)]) == 9)

    # Window constraints:
    # Riga: present exactly on days 5-8
    riga = idx["Riga"]
    for day in range(1, N_DAYS + 1):
        d = day - 1
        if 5 <= day <= 8:
            s.add(present_expr(riga, d))
        else:
            s.add(Not(present_expr(riga, d)))
    # Tallinn: present exactly on days 18-20
    tallinn = idx["Tallinn"]
    for day in range(1, N_DAYS + 1):
        d = day - 1
        if 18 <= day <= 20:
            s.add(present_expr(tallinn, d))
        else:
            s.add(Not(present_expr(tallinn, d)))
    # Milan: present exactly on days 24-26
    milan = idx["Milan"]
    for day in range(1, N_DAYS + 1):
        d = day - 1
        if 24 <= day <= 26:
            s.add(present_expr(milan, d))
        else:
            s.add(Not(present_expr(milan, d)))

    # Durations for other cities must match required totals
    for cname, total in required_days.items():
        c = idx[cname]
        # For Riga, Tallinn, Milan, windows already enforce exact presence; still enforce the totals for safety
        s.add(Sum([If(present_expr(c, d), 1, 0) for d in range(N_DAYS)]) == total)

    # Ensure each city is an end-of-day location at least once (creates clear itinerary segments and ensures exactly 10 segments)
    for c in range(len(cities)):
        s.add(Or(*[end_of_day[d] == c for d in range(N_DAYS)]))

    # Optional: minimize a simple objective to get a deterministic solution
    s.minimize(Sum([end_of_day[d] for d in range(N_DAYS)]))

    if s.check() != sat:
        print(json.dumps({"error": "No feasible itinerary found"}))
        return

    m = s.model()
    ends = [m.evaluate(end_of_day[d]).as_long() for d in range(N_DAYS)]

    # Build aggregated itinerary ranges by contiguous end-of-day city segments
    itinerary = []
    start = 1
    curr = ends[0]
    for d in range(1, N_DAYS):
        if ends[d] != curr:
            itinerary.append({
                "day_range": f"Day {start}-{d}",
                "place": cities[curr]
            })
            start = d + 1
            curr = ends[d]
    itinerary.append({
        "day_range": f"Day {start}-{N_DAYS}",
        "place": cities[curr]
    })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()