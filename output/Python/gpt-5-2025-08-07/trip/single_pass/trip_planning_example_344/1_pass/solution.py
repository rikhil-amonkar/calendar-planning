import json
import itertools

def overlap_days(a_start, a_end, b_start, b_end):
    return max(0, min(a_end, b_end) - max(a_start, b_start) + 1)

def build_itinerary(order, req_days, total_days):
    # With shared transition days: boundaries determined by required days
    c1, c2, c3, c4 = order
    b1 = req_days[c1]                         # end of segment 1
    b2 = b1 - 1 + req_days[c2]               # end of segment 2
    b3 = b2 - 1 + req_days[c3]               # end of segment 3
    # Segment 4 ends at total_days
    segs = {
        c1: (1, b1),
        c2: (b1, b2),
        c3: (b2, b3),
        c4: (b3, total_days),
    }
    return segs

def main():
    # Input variables (trip constraints)
    total_days = 20
    cities = ["Valencia", "Athens", "Naples", "Zurich"]
    required_days = {
        "Valencia": 6,
        "Athens": 6,
        "Naples": 5,
        "Zurich": 6
    }

    # Directed flight availability inferred from the description
    flights = {
        "Valencia": {"Naples", "Athens", "Zurich"},
        "Athens": {"Naples", "Zurich"},
        "Naples": {"Valencia", "Athens", "Zurich"},
        "Zurich": {"Naples", "Athens", "Valencia"}
    }

    # Special window constraints (inclusive)
    window_athens = (1, 6)   # want to visit relatives in Athens between day 1 and 6
    window_naples = (16, 20) # wedding in Naples between day 16 and 20

    # Basic feasibility check: sum of city-days must equal total_days + number_of_transitions
    num_cities = len(cities)
    transitions = num_cities - 1
    if sum(required_days[c] for c in cities) != total_days + transitions:
        raise ValueError("City-day requirements are inconsistent with total days and transitions.")

    # We require a 4-city trip; Naples has 5 days, so it must be the last segment (which is 5 days)
    # Explore permutations for the first three cities
    best_plan = None
    best_score = None

    others = [c for c in cities if c != "Naples"]
    for perm in itertools.permutations(others, 3):
        order = list(perm) + ["Naples"]

        # Build itinerary segments with shared transition days
        segs = build_itinerary(order, required_days, total_days)

        # Validate that segment lengths match exactly the required days
        valid_lengths = all((segs[c][1] - segs[c][0] + 1) == required_days[c] for c in cities)
        if not valid_lengths:
            continue

        # Validate direct flights for the ordered transitions
        flights_ok = True
        for i in range(3):
            a, b = order[i], order[i+1]
            if b not in flights.get(a, set()):
                flights_ok = False
                break
        if not flights_ok:
            continue

        # Window constraints: must be in Athens between day 1 and 6 (at least 1 day overlap)
        ath_s, ath_e = segs["Athens"]
        ath_overlap = overlap_days(ath_s, ath_e, window_athens[0], window_athens[1])

        # Wedding window: must be in Naples between day 16 and 20 (at least 1 day overlap)
        nap_s, nap_e = segs["Naples"]
        nap_overlap = overlap_days(nap_s, nap_e, window_naples[0], window_naples[1])

        if ath_overlap < 1 or nap_overlap < 1:
            continue

        # Scoring: maximize overlap with preferred windows; strong bonus for exact alignment
        score = ath_overlap + nap_overlap
        if ath_overlap == (window_athens[1] - window_athens[0] + 1) and (ath_s, ath_e) == window_athens:
            score += 1000
        if nap_overlap == (window_naples[1] - window_naples[0] + 1) and (nap_s, nap_e) == window_naples:
            score += 1000

        # Tie-breaker: prefer orders that start with Athens (visiting relatives early)
        if order[0] == "Athens":
            score += 10

        if best_score is None or score > best_score:
            best_score = score
            best_plan = segs

    if not best_plan:
        raise RuntimeError("No feasible itinerary found given the constraints.")

    # Build JSON-friendly output
    itinerary_list = []
    # Sort segments by start day
    for city, (start, end) in sorted(best_plan.items(), key=lambda x: x[1][0]):
        itinerary_list.append({
            "day_range": f"Day {start}-{end}",
            "place": city
        })

    result = {"itinerary": itinerary_list}
    print(json.dumps(result))

if __name__ == "__main__":
    main()