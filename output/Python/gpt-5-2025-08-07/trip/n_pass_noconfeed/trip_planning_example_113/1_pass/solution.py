import json
import itertools

def compute_itinerary():
    # Input variables (constraints)
    total_days = 12
    cities = ["Naples", "Milan", "Seville"]
    required_days = {
        "Naples": 3,
        "Milan": 7,
        "Seville": 4
    }
    # Direct flights (undirected edges)
    direct_pairs = [
        ("Milan", "Seville"),
        ("Naples", "Milan")
    ]
    # Normalize to undirected adjacency
    direct_flights = {}
    for a, b in direct_pairs:
        direct_flights.setdefault(a, set()).add(b)
        direct_flights.setdefault(b, set()).add(a)

    # Show constraint
    show_city = "Seville"
    show_start = 9
    show_end = 12  # inclusive

    # Basic feasibility check: unique days + (k-1) transitions must match sum of required days
    k = len(cities)
    sum_required = sum(required_days[c] for c in cities)
    min_transitions_needed = sum_required - total_days
    if min_transitions_needed != (k - 1):
        raise ValueError("Constraints infeasible: number of transitions needed does not match number of city changes.")

    def valid_order(order):
        # Check flight adjacency between consecutive cities
        for i in range(len(order) - 1):
            if order[i+1] not in direct_flights.get(order[i], set()):
                return False
        return True

    def build_timeline(order):
        # Compute overlapping day ranges given the order and required days
        # With k=3 and (k-1)=2 transitions:
        # Segment 0: days 1 .. r0
        # Segment 1: days r0 .. r0 + r1 - 1
        # Segment 2: days r0 + r1 - 1 .. total_days
        r0 = required_days[order[0]]
        r1 = required_days[order[1]]
        r2 = required_days[order[2]]

        t1 = r0  # first flight day (end of city 0, start of city 1)
        t2 = r0 + r1 - 1  # second flight day (end of city 1, start of city 2)

        segs = {
            order[0]: (1, t1),
            order[1]: (t1, t2),
            order[2]: (t2, total_days)
        }
        return segs

    def satisfies_show(segs):
        s_start, s_end = segs[show_city]
        # Show days must all be within the show city's segment (inclusive)
        return s_start <= show_start and s_end >= show_end

    # Try all orders that are valid given direct flights and show constraint
    best = None
    for order in itertools.permutations(cities):
        if not valid_order(order):
            continue
        segs = build_timeline(order)
        if satisfies_show(segs):
            best = (order, segs)
            break

    if best is None:
        raise ValueError("No valid itinerary found that satisfies all constraints.")

    order, segs = best

    # Build output in the specified JSON format
    itinerary = []
    for city in order:
        start, end = segs[city]
        itinerary.append({
            "day_range": f"Day {start}-{end}",
            "place": city
        })

    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = compute_itinerary()
    print(json.dumps(result, ensure_ascii=False))