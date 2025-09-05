import json
from z3 import Int, Bool, Optimize, Or, And, Not, Implies, If, Sum, sat, is_true

def main():
    # Define constants
    num_days = 12
    cities = ["Brussels", "Barcelona", "Split"]
    BRU, BAR, SPL = 0, 1, 2

    # Trip requirements (as variables for clarity)
    required_days = {
        BRU: 2,   # Brussels
        BAR: 7,   # Barcelona
        SPL: 5    # Split
    }
    conference_days_in_Brussels = [1, 2]

    # Z3 variables
    days = list(range(1, num_days + 1))
    start_city = {d: Int(f"start_city_{d}") for d in days}
    end_city = {d: Int(f"end_city_{d}") for d in days}
    flight = {d: Bool(f"flight_{d}") for d in days}
    init_city = Int("init_city")
    in_city = {(d, c): Bool(f"in_city_d{d}_c{c}") for d in days for c in (BRU, BAR, SPL)}

    opt = Optimize()

    # Domain constraints: cities indices within range
    for d in days:
        opt.add(And(0 <= start_city[d], start_city[d] <= 2))
        opt.add(And(0 <= end_city[d], end_city[d] <= 2))
    opt.add(And(0 <= init_city, init_city <= 2))

    # Day-to-day continuity: start of day d is end of day d-1
    opt.add(start_city[1] == init_city)
    for d in range(2, num_days + 1):
        opt.add(start_city[d] == end_city[d - 1])

    # Adjacency (direct flights) between cities
    def adjacent(a, b):
        return Or(
            And(a == BRU, b == BAR),
            And(a == BAR, b == BRU),
            And(a == BAR, b == SPL),
            And(a == SPL, b == BAR)
        )

    # Flight constraints: at most one direct flight per day between adjacent cities
    for d in days:
        opt.add(Implies(flight[d], And(start_city[d] != end_city[d], adjacent(start_city[d], end_city[d]))))
        opt.add(Implies(Not(flight[d]), start_city[d] == end_city[d]))

    # Presence constraints: On day d, traveler is in start_city[d] and end_city[d]
    for d in days:
        for c in (BRU, BAR, SPL):
            opt.add(in_city[(d, c)] == Or(start_city[d] == c, end_city[d] == c))

    # City-day counts
    for c in (BRU, BAR, SPL):
        total_days_in_c = Sum([If(in_city[(d, c)], 1, 0) for d in days])
        opt.add(total_days_in_c == required_days[c])

    # Conference days: must be in Brussels on day 1 and 2
    for d in conference_days_in_Brussels:
        opt.add(in_city[(d, BRU)] == True)

    # Optimization objectives:
    # 1) Minimize number of flight days
    total_flights = Sum([If(flight[d], 1, 0) for d in days])
    opt.minimize(total_flights)
    # 2) Among minimal flights, prefer earlier flights
    sum_flight_day_indices = Sum([If(flight[d], d, 0) for d in days])
    opt.minimize(sum_flight_day_indices)

    # Solve
    if opt.check() != sat:
        print(json.dumps({"itinerary": []}))
        return
    m = opt.model()

    # Extract presence per city per day
    presence = {c: [] for c in (BRU, BAR, SPL)}
    for d in days:
        for c in (BRU, BAR, SPL):
            if is_true(m.eval(in_city[(d, c)])):
                presence[c].append(d)

    # Convert presence lists to contiguous day ranges
    def to_ranges(day_list):
        if not day_list:
            return []
        day_list = sorted(day_list)
        ranges = []
        start = prev = day_list[0]
        for day in day_list[1:]:
            if day == prev + 1:
                prev = day
            else:
                ranges.append((start, prev))
                start = prev = day
        ranges.append((start, prev))
        return ranges

    itinerary_entries = []
    for c in (BRU, BAR, SPL):
        for (s, e) in to_ranges(presence[c]):
            itinerary_entries.append({"start": s, "end": e, "place": cities[c]})

    # Sort ranges by start day (chronological order)
    itinerary_entries.sort(key=lambda x: (x["start"], x["end"]))

    # Format output
    itinerary = []
    for entry in itinerary_entries:
        s, e, place = entry["start"], entry["end"], entry["place"]
        itinerary.append({"day_range": f"Day {s}-{e}", "place": place})

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()