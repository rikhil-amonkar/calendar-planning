import json
from itertools import permutations

def build_adjacency(direct_flights):
    adj = {}
    for a, b in direct_flights:
        adj.setdefault(a, set()).add(b)
        adj.setdefault(b, set()).add(a)
    return adj

def presence_on_day(order, f1, f2, day):
    start, mid, end = order
    if day < f1:
        return {start}
    elif day == f1:
        return {start, mid}
    elif f1 < day < f2:
        return {mid}
    elif day == f2:
        return {mid, end}
    else:
        return {end}

def compute_itinerary(total_days, desired_days, must_be_in, direct_flights):
    # Preprocess
    cities = list(desired_days.keys())
    visited = [c for c, d in desired_days.items() if d > 0]
    adjacency = build_adjacency(direct_flights)
    sum_desired = sum(desired_days.values())
    flights_needed = sum_desired - total_days

    # Basic feasibility checks
    if flights_needed < 0:
        raise ValueError("Infeasible: desired days sum less than total days.")
    if len(visited) < 1:
        raise ValueError("No cities to visit.")
    # For visiting k cities in a simple path, at least (k-1) flights are required.
    if flights_needed != len(visited) - 1:
        # Not strictly impossible, but outside the simple-path assumption used here.
        # We'll still attempt brute-force over path permutations of length len(visited).
        pass

    # Generate Hamiltonian paths over visited cities that follow direct flights
    candidate_orders = []
    for perm in permutations(visited):
        ok = True
        for i in range(len(perm) - 1):
            if perm[i+1] not in adjacency.get(perm[i], set()):
                ok = False
                break
        if ok:
            candidate_orders.append(perm)

    # Try to solve using algebra derived from overlap counts
    # For three cities and two flights, order is (start, mid, end)
    # Flight days: f1 = desired[start], f2 = total_days - desired[end] + 1
    for order in candidate_orders:
        if len(order) != 3:
            continue  # This solver targets exactly 3 cities (as per the problem)
        start, mid, end = order
        dS = desired_days[start]
        dM = desired_days[mid]
        dE = desired_days[end]
        f1 = dS
        f2 = total_days - dE + 1

        # Validate flight day positions
        if not (1 <= f1 < f2 <= total_days):
            continue

        # Validate mid city count from overlap formula: dM should equal (f2 - f1 + 1)
        if dM != (f2 - f1 + 1):
            continue

        # Validate must-be-in constraints
        all_ok = True
        for day, req_city in must_be_in.items():
            present = presence_on_day(order, f1, f2, day)
            if req_city not in present:
                all_ok = False
                break
        if not all_ok:
            continue

        # Build itinerary segments (note: flight days appear in both adjacent segments)
        itinerary = [
            {"day_range": f"Day 1-{f1}", "place": start},
            {"day_range": f"Day {f1}-{f2}", "place": mid},
            {"day_range": f"Day {f2}-{total_days}", "place": end},
        ]
        return {"itinerary": itinerary}

    # If algebraic approach failed, attempt a simple day-by-day brute force (fallback)
    # State representation: (day, current_city, flights_used, order_so_far, f_days)
    # Where order_so_far is the list of cities in the path (without repeats), f_days are flight days
    # We keep at most one flight per day and ensure counts match at the end.
    # Given the specific problem, this branch should not be needed, but kept for completeness.

    def brute_force():
        # Build all path orders first (already in candidate_orders)
        for order in candidate_orders:
            if len(order) != 3:
                continue
            start, mid, end = order
            # Try all possible flight day pairs (f1, f2)
            for f1 in range(1, total_days):
                for f2 in range(f1 + 1, total_days + 1):
                    # Counts by formula
                    countS = f1
                    countM = f2 - f1 + 1
                    countE = total_days - f2 + 1
                    if countS != desired_days[start] or countM != desired_days[mid] or countE != desired_days[end]:
                        continue
                    # Check must-be-in
                    ok = True
                    for day, req_city in must_be_in.items():
                        if req_city not in presence_on_day(order, f1, f2, day):
                            ok = False
                            break
                    if not ok:
                        continue
                    itinerary = [
                        {"day_range": f"Day 1-{f1}", "place": start},
                        {"day_range": f"Day {f1}-{f2}", "place": mid},
                        {"day_range": f"Day {f2}-{total_days}", "place": end},
                    ]
                    return {"itinerary": itinerary}
        return {"itinerary": []}

    return brute_force()

if __name__ == "__main__":
    # Input variables based on the problem statement
    total_days = 9
    desired_days = {
        "Mykonos": 6,
        "Budapest": 3,
        "Hamburg": 2
    }
    must_be_in = {
        4: "Mykonos",
        9: "Mykonos"
    }
    direct_flights = [
        ("Budapest", "Mykonos"),
        ("Hamburg", "Budapest")
    ]

    result = compute_itinerary(total_days, desired_days, must_be_in, direct_flights)
    print(json.dumps(result, ensure_ascii=False))