import itertools
import json

def compute_itinerary():
    # Input variables (constraints)
    total_days = 12
    city_stay_requirements = {
        "Hamburg": 2,
        "Zurich": 3,
        "Helsinki": 2,
        "Bucharest": 2,
        "Split": 7,
    }
    must_attend_on_days = {
        "Split": {4, 10}  # must be in Split on day 4 and day 10
    }
    must_attend_between = {
        "Zurich": (1, 3)  # must be in Zurich on at least one day between 1 and 3 (inclusive)
    }
    direct_flights_pairs = [
        ("Zurich", "Helsinki"),
        ("Hamburg", "Bucharest"),
        ("Helsinki", "Hamburg"),
        ("Zurich", "Hamburg"),
        ("Zurich", "Bucharest"),
        ("Zurich", "Split"),
        ("Helsinki", "Split"),
        ("Split", "Hamburg"),
    ]

    # Preprocess flight edges as undirected
    direct_edges = set(frozenset(edge) for edge in direct_flights_pairs)

    cities = list(city_stay_requirements.keys())
    N = len(cities)

    # Validate high-level feasibility: sum of requested city-days - (number of flights) must equal total days
    # With overlap rule, total unique trip days D = sum(city_days) - (segments - 1)
    S = sum(city_stay_requirements.values())
    if S - (N - 1) != total_days:
        # If infeasible by basic arithmetic, return no itinerary
        return None

    def build_schedule(order):
        # Build overlapping segments per city in given order
        segments = []
        start = 1
        for city in order:
            dur = city_stay_requirements[city]
            end = start + dur - 1
            segments.append((city, start, end))
            start = end  # next segment starts on the same day (flight day overlap)
        return segments

    def presence_map(segments):
        presence = {day: set() for day in range(1, total_days + 1)}
        for city, s, e in segments:
            for d in range(s, e + 1):
                presence[d].add(city)
        return presence

    # Search over permutations for a valid itinerary
    for order in itertools.permutations(cities):
        # Ensure direct flights between consecutive cities
        valid_edges = True
        for i in range(N - 1):
            if frozenset({order[i], order[i + 1]}) not in direct_edges:
                valid_edges = False
                break
        if not valid_edges:
            continue

        segments = build_schedule(order)
        # Ensure the schedule ends on the intended total_days
        if segments[-1][2] != total_days:
            continue

        present = presence_map(segments)

        # Check must-attend-on-days constraints
        on_days_ok = True
        for city, days in must_attend_on_days.items():
            for d in days:
                if city not in present.get(d, set()):
                    on_days_ok = False
                    break
            if not on_days_ok:
                break
        if not on_days_ok:
            continue

        # Check must-attend-between constraints (at least one day in range)
        between_ok = True
        for city, (a, b) in must_attend_between.items():
            if not any(city in present.get(d, set()) for d in range(a, b + 1)):
                between_ok = False
                break
        if not between_ok:
            continue

        # All constraints satisfied; format itinerary
        itinerary = []
        for city, s, e in segments:
            itinerary.append({"day_range": f"Day {s}-{e}", "place": city})
        return {"itinerary": itinerary}

    return None

def main():
    result = compute_itinerary()
    if result is None:
        print(json.dumps({"error": "No valid itinerary found given constraints"}))
    else:
        print(json.dumps(result))

if __name__ == "__main__":
    main()