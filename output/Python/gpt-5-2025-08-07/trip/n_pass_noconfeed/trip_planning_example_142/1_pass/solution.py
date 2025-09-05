import itertools
import json

def compute_itinerary():
    # Input variables (trip constraints)
    total_days = 7
    required_days = {
        "Madrid": 4,
        "Dublin": 3,
        "Tallinn": 2
    }
    cities = ["Madrid", "Dublin", "Tallinn"]
    # Direct flights (undirected)
    direct_routes = {frozenset(["Madrid", "Dublin"]), frozenset(["Dublin", "Tallinn"])}
    # Workshop constraint: must be in Tallinn on both day 6 and day 7
    workshop_city = "Tallinn"
    workshop_days = {6, 7}

    # Helper to check if there is a direct flight between two cities
    def has_direct(a, b):
        return frozenset([a, b]) in direct_routes

    # Validate sum of required days aligns with flight-count overlap
    expected_flights = len(cities) - 1
    if sum(required_days[c] for c in cities) != total_days + expected_flights:
        raise ValueError("Constraints inconsistent: sum of required city-days must equal total_days + number_of_flights.")

    # Try all permutations consistent with direct flights and workshop constraint
    best_itinerary = None
    for order in itertools.permutations(cities, 3):
        # Must have direct flights between consecutive cities
        if not (has_direct(order[0], order[1]) and has_direct(order[1], order[2])):
            continue

        # Compute transition days using overlap rule
        # City1 covers Day 1..d1
        # City2 covers Day d1..d2
        # City3 covers Day d2..total_days
        c1 = required_days[order[0]]
        c2 = required_days[order[1]]
        c3 = required_days[order[2]]

        d1 = c1
        d2 = c1 + c2 - 1

        # Validate boundaries
        if not (1 <= d1 <= total_days and d1 <= d2 <= total_days):
            continue

        segs = [
            {"place": order[0], "start": 1, "end": d1},
            {"place": order[1], "start": d1, "end": d2},
            {"place": order[2], "start": d2, "end": total_days},
        ]

        # Validate lengths match required days
        def seg_len(s): return s["end"] - s["start"] + 1
        lengths_ok = (
            seg_len(segs[0]) == c1 and
            seg_len(segs[1]) == c2 and
            seg_len(segs[2]) == c3
        )
        if not lengths_ok:
            continue

        # Validate workshop days are in Tallinn's segment
        tallinn_seg = next(s for s in segs if s["place"] == workshop_city)
        tallinn_days = set(range(tallinn_seg["start"], tallinn_seg["end"] + 1))
        if not workshop_days.issubset(tallinn_days):
            continue

        # Found a valid itinerary; choose the first valid as optimal
        best_itinerary = segs
        break

    if best_itinerary is None:
        # Fallback: no valid plan found (should not happen with given constraints)
        result = {"itinerary": []}
    else:
        # Format output
        itinerary_output = []
        for seg in best_itinerary:
            itinerary_output.append({
                "day_range": f"Day {seg['start']}-{seg['end']}",
                "place": seg["place"]
            })
        result = {"itinerary": itinerary_output}

    print(json.dumps(result, ensure_ascii=False))

if __name__ == "__main__":
    compute_itinerary()