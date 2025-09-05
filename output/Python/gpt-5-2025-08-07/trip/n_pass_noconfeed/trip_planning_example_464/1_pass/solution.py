import itertools
import json

def main():
    # Input variables
    total_days = 18
    cities = ["Krakow", "Frankfurt", "Oslo", "Dubrovnik", "Naples"]
    durations = {
        "Krakow": 5,
        "Frankfurt": 4,
        "Oslo": 3,
        "Dubrovnik": 5,
        "Naples": 5,
    }
    # Direct flight pairs (undirected)
    direct_flights = {
        frozenset(("Dubrovnik", "Oslo")),
        frozenset(("Frankfurt", "Krakow")),
        frozenset(("Frankfurt", "Oslo")),
        frozenset(("Dubrovnik", "Frankfurt")),
        frozenset(("Krakow", "Oslo")),
        frozenset(("Naples", "Oslo")),
        frozenset(("Naples", "Dubrovnik")),
        frozenset(("Naples", "Frankfurt")),
    }

    # Special window constraints
    friends_city = "Dubrovnik"
    friends_window = (5, 9)  # inclusive
    relatives_city = "Oslo"
    relatives_window = (16, 18)  # inclusive

    # Quick feasibility check: total calendar days equals sum(durations) - (transitions)
    # For visiting all cities in a single chain, transitions = number_of_cities - 1
    if sum(durations[c] for c in cities) - (len(cities) - 1) != total_days:
        raise ValueError("Infeasible total days with given durations and overlap rule.")

    def has_direct_flights(sequence):
        for i in range(1, len(sequence)):
            if frozenset((sequence[i-1], sequence[i])) not in direct_flights:
                return False
        return True

    def compute_day_ranges(sequence):
        # Using the overlap rule: start_next = end_prev (shared day)
        day_ranges = {}
        current_start = 1
        for idx, city in enumerate(sequence):
            d = durations[city]
            if idx == 0:
                start = current_start
            else:
                # start equals previous end (shared flight day)
                start = current_start
            end = start + d - 1
            day_ranges[city] = (start, end)
            # Next city's start equals this end (overlap on transition day)
            current_start = end
        return day_ranges

    def satisfies_windows(day_ranges):
        fs, fe = day_ranges[friends_city]
        rs, re = day_ranges[relatives_city]
        # Need to be in friends_city for entire friends_window
        if not (fs <= friends_window[0] and fe >= friends_window[1]):
            return False
        # Need to be in relatives_city for entire relatives_window
        if not (rs <= relatives_window[0] and re >= relatives_window[1]):
            return False
        # Additionally, ensure the trip exactly spans total_days from Day 1 to Day total_days
        overall_start = min(s for s, e in day_ranges.values())
        overall_end = max(e for s, e in day_ranges.values())
        if not (overall_start == 1 and overall_end == total_days):
            return False
        return True

    valid_plan = None
    for sequence in itertools.permutations(cities):
        if not has_direct_flights(sequence):
            continue
        day_ranges = compute_day_ranges(sequence)
        if satisfies_windows(day_ranges):
            # Also ensure that each city is allocated exactly its intended duration
            # Duration in city is end - start + 1 by construction
            ok_durations = all((day_ranges[c][1] - day_ranges[c][0] + 1) == durations[c] for c in sequence)
            if not ok_durations:
                continue
            valid_plan = [(city, day_ranges[city]) for city in sequence]
            break

    if not valid_plan:
        raise RuntimeError("No valid itinerary found that satisfies all constraints.")

    # Build itinerary output
    itinerary = []
    for city, (start, end) in valid_plan:
        itinerary.append({
            "day_range": f"Day {start}-{end}",
            "place": city
        })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()