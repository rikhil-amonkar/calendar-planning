import itertools
import json

def compute_itinerary():
    # Input variables (constraints)
    total_days = 14
    cities = ["Amsterdam", "Vienna", "Santorini", "Lyon"]
    desired_stays = {
        "Amsterdam": 3,
        "Vienna": 7,
        "Santorini": 4,
        "Lyon": 3,
    }
    # Direct flights (undirected)
    direct_flights = {
        ("Vienna", "Lyon"),
        ("Vienna", "Santorini"),
        ("Vienna", "Amsterdam"),
        ("Amsterdam", "Santorini"),
        ("Lyon", "Amsterdam"),
    }
    flight_edges = {frozenset(edge) for edge in direct_flights}

    # Event windows: city must include the full window (inclusive)
    # Workshop in Amsterdam between day 9 and day 11 (inclusive)
    # Wedding in Lyon between day 7 and day 9 (inclusive)
    event_windows = {
        "Amsterdam": (9, 11),
        "Lyon": (7, 9),
    }

    # Basic feasibility checks
    if sum(desired_stays.values()) != total_days + (len(cities) - 1):
        # Sum of desired stays must equal total days + number of transitions (overlap days)
        return None

    def is_direct(a, b):
        return frozenset((a, b)) in flight_edges

    def compute_intervals(order):
        # Overlap rule: if moving from city A to city B on day X, then both include day X.
        # Implementation: consecutive city intervals overlap by exactly one day
        intervals = {}
        start = 1
        for i, city in enumerate(order):
            dur = desired_stays[city]
            if i == 0:
                city_start = start
            else:
                # Overlap one day with previous city's end
                prev_end = intervals[order[i - 1]][1]
                city_start = prev_end
            city_end = city_start + dur - 1
            intervals[city] = (city_start, city_end)
        return intervals

    def valid_order(order):
        # Check path uses only direct flights
        for a, b in zip(order, order[1:]):
            if not is_direct(a, b):
                return False
        return True

    def satisfies_events(intervals):
        for city, (req_start, req_end) in event_windows.items():
            c_start, c_end = intervals[city]
            if not (c_start <= req_start and c_end >= req_end):
                return False
        return True

    def union_ends(intervals, order):
        # The union of days should be exactly total_days, ending on day total_days
        first_city = order[0]
        last_city = order[-1]
        start = intervals[first_city][0]
        end = intervals[last_city][1]
        return start == 1 and end == total_days

    solutions = []
    for order in itertools.permutations(cities):
        if not valid_order(order):
            continue
        intervals = compute_intervals(order)
        # Ensure interval lengths equal desired stays
        lengths_ok = all((intervals[c][1] - intervals[c][0] + 1) == desired_stays[c] for c in cities)
        if not lengths_ok:
            continue
        # Ensure union spans exactly total_days from day 1 to total_days
        if not union_ends(intervals, order):
            continue
        # Ensure event windows satisfied
        if not satisfies_events(intervals):
            continue
        solutions.append((order, intervals))

    if not solutions:
        return None

    # Select an "optimal" solution - here we choose the first valid by lexicographic order of the itinerary tuple
    solutions.sort(key=lambda x: x[0])
    order, intervals = solutions[0]

    itinerary = []
    for city in order:
        start, end = intervals[city]
        itinerary.append({
            "day_range": f"Day {start}-{end}",
            "place": city
        })

    return {"itinerary": itinerary}

def main():
    result = compute_itinerary()
    if result is None:
        print(json.dumps({"error": "No feasible itinerary found with given constraints"}))
    else:
        print(json.dumps(result))

if __name__ == "__main__":
    main()