import itertools
import json

def main():
    # Input variables (trip constraints)
    total_days = 13
    cities = ["Madrid", "Seville", "Porto", "Stuttgart"]
    required_stays = {
        "Seville": 2,
        "Stuttgart": 7,
        "Porto": 3,
        "Madrid": 4
    }
    conference_days_in_stuttgart = {7, 13}
    relatives_city = "Madrid"
    relatives_window = (1, 4)  # inclusive

    # Direct flights (undirected)
    direct_pairs = {
        ("Porto", "Stuttgart"),
        ("Seville", "Porto"),
        ("Madrid", "Porto"),
        ("Madrid", "Seville")
    }
    def direct(a, b):
        return (a, b) in direct_pairs or (b, a) in direct_pairs

    # Basic feasibility check: sum(city_days) must equal total_days + number_of_flights (3)
    flights_needed = len(cities) - 1  # visiting 4 cities with contiguous stays -> 3 flights
    if sum(required_stays[c] for c in cities) != total_days + flights_needed:
        print(json.dumps({"itinerary": []}))
        return

    # Generate all feasible city orders that end in Stuttgart and traverse only direct flights
    best_plan = None
    best_score = None

    for perm in itertools.permutations([c for c in cities if c != "Stuttgart"]):
        order = list(perm) + ["Stuttgart"]

        # Ensure consecutive cities have direct flights
        if not all(direct(order[i], order[i+1]) for i in range(len(order) - 1)):
            continue

        # Compute flight days based on required stays:
        # If order is [C1, C2, C3, C4], with flight days f1, f2, f3:
        # C1 occupies days [1..f1], C2 [f1..f2], C3 [f2..f3], C4 [f3..total_days]
        d1 = required_stays[order[0]]
        d2 = required_stays[order[1]]
        d3 = required_stays[order[2]]
        d4_required = required_stays[order[3]]

        f1 = d1
        f2 = d1 + d2 - 1
        f3 = d1 + d2 + d3 - 2

        # Validate day ranges and last segment length
        if not (1 <= f1 < f2 < f3 <= total_days):
            continue

        d4 = total_days - f3 + 1
        if d4 != d4_required:
            continue

        # Check conference days in Stuttgart: must be in [f3..total_days]
        if not all(f3 <= day <= total_days for day in conference_days_in_stuttgart):
            continue

        # Check relatives window presence in Madrid: intersection with [1..4] must be non-empty
        # Determine Madrid's occupied interval
        segments = [
            (order[0], 1, f1),
            (order[1], f1, f2),
            (order[2], f2, f3),
            (order[3], f3, total_days)
        ]
        madrid_interval = next((start, end) for city, start, end in segments if city == relatives_city)
        rel_start, rel_end = relatives_window
        earliest_madrid_in_window = max(rel_start, madrid_interval[0])
        if earliest_madrid_in_window > min(rel_end, madrid_interval[1]):
            # No overlap with [rel_start..rel_end]
            continue

        # Compute score: earlier Madrid presence is better; prefer starting in Madrid if tie
        score = (
            earliest_madrid_in_window,  # lower is better
            0 if order[0] == "Madrid" else 1
        )

        if best_score is None or score < best_score:
            best_score = score
            best_plan = segments

    if best_plan is None:
        print(json.dumps({"itinerary": []}))
        return

    # Build output structure
    itinerary = []
    for city, start, end in best_plan:
        itinerary.append({"day_range": f"Day {start}-{end}", "place": city})

    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()