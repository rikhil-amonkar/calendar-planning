import json
from z3 import *

def main():
    # Parameters (input variables)
    total_days = 16
    cities = ["London", "Split", "Oslo", "Porto"]
    city_index = {name: i for i, name in enumerate(cities)}
    durations_required = {
        "London": 7,
        "Split": 5,
        "Oslo": 2,
        "Porto": 5
    }
    # Event: must be in Split on days 7..11 inclusive
    split_show_start = 7
    split_show_end = 11
    # London relatives window: London days must be within 1..7
    london_window_start = 1
    london_window_end = 7

    # Direct flight pairs (undirected)
    direct_pairs = {
        ("London", "Oslo"),
        ("Split", "Oslo"),
        ("Oslo", "Porto"),
        ("London", "Split")
    }
    direct_pairs_idx = {(city_index[a], city_index[b]) for a, b in direct_pairs}
    direct_pairs_idx |= {(b, a) for (a, b) in direct_pairs_idx}

    # Z3 variables
    # City at the end of each day (1-based days -> 0-based index storage)
    city_end = [Int(f"city_end_{d}") for d in range(1, total_days + 1)]

    s = Solver()

    # Domain constraints for city_end
    for d in range(total_days):
        s.add(And(city_end[d] >= 0, city_end[d] < len(cities)))

    # Transition constraints: if city changes, it must be a direct flight
    for d in range(1, total_days):
        s.add(Implies(city_end[d] != city_end[d - 1],
                      Or(*[And(city_end[d - 1] == a, city_end[d] == b) for (a, b) in direct_pairs_idx])))

    # Presence booleans: present[c][d] indicates presence in city c on day d (1-based)
    present = {
        c: [Bool(f"present_{c}_{day}") for day in range(1, total_days + 1)]
        for c in range(len(cities))
    }

    # Define presence logic:
    # present[c][d] is true if:
    # - city_end[d] == c, OR
    # - d > 1 AND city_end[d-1] == c AND city_end[d] != city_end[d-1] (travel day counts for both cities)
    for c in range(len(cities)):
        for d in range(total_days):
            if d == 0:
                s.add(present[c][d] == (city_end[d] == c))
            else:
                s.add(present[c][d] ==
                      Or(city_end[d] == c,
                         And(city_end[d - 1] == c, city_end[d] != city_end[d - 1])))

    # Duration constraints per city
    for name, req in durations_required.items():
        c = city_index[name]
        s.add(Sum([If(present[c][d], 1, 0) for d in range(total_days)]) == req)

    # London presence must be within 1..7; i.e., no London presence after day 7
    london_idx = city_index["London"]
    for d in range(total_days):
        day_num = d + 1
        if day_num < london_window_start or day_num > london_window_end:
            s.add(present[london_idx][d] == False)

    # Must be in Split on days 7..11 inclusive (to attend the show)
    split_idx = city_index["Split"]
    for day in range(split_show_start, split_show_end + 1):
        s.add(present[split_idx][day - 1] == True)

    # Enforce the implied relation: total durations sum equals total_days + number_of_transitions
    total_required_days = sum(durations_required.values())
    transitions = [If(city_end[d] != city_end[d - 1], 1, 0) for d in range(1, total_days)]
    s.add(Sum(transitions) == total_required_days - total_days)

    # Ensure each day has at least one city presence (redundant but explicit)
    for d in range(total_days):
        s.add(Or(*[present[c][d] for c in range(len(cities))]))

    # Solve
    if s.check() != sat:
        print(json.dumps({"itinerary": []}))
        return

    m = s.model()

    # Evaluate presence matrix
    presence_eval = {
        cities[c]: [is_true(m.evaluate(present[c][d])) for d in range(total_days)]
        for c in range(len(cities))
    }

    # Build itinerary as contiguous presence intervals for each city, sorted chronologically
    intervals = []
    for city_name, days_presence in presence_eval.items():
        start = None
        for d in range(total_days):
            if days_presence[d] and start is None:
                start = d + 1
            if (start is not None) and (not days_presence[d] or d == total_days - 1):
                end_day = d + 1 if days_presence[d] and d == total_days - 1 else d
                intervals.append((start, end_day, city_name))
                start = None

    # Sort by start day
    intervals.sort(key=lambda x: x[0])

    # Format output
    itinerary_output = []
    for (start, end, city) in intervals:
        itinerary_output.append({
            "day_range": f"Day {start}-{end}",
            "place": city
        })

    print(json.dumps({"itinerary": itinerary_output}, ensure_ascii=False))

if __name__ == "__main__":
    main()