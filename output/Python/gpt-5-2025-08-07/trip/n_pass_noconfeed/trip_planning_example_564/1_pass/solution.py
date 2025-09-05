import itertools
import json

def main():
    # Input variables (trip constraints)
    total_days = 16
    cities = ["Rome", "Seville", "Istanbul", "Naples", "Santorini"]
    durations = {
        "Istanbul": 2,
        "Rome": 3,
        "Seville": 4,
        "Naples": 7,
        "Santorini": 4,
    }
    # Fixed presence windows: inclusive day ranges that must match exactly
    fixed_windows = {
        "Istanbul": (6, 7),     # visit relatives between day 6 and 7
        "Santorini": (13, 16),  # wedding between day 13 and 16
    }
    # Direct flight pairs (undirected)
    direct_pairs = [
        ("Rome", "Santorini"),
        ("Seville", "Rome"),
        ("Istanbul", "Naples"),
        ("Naples", "Santorini"),
        ("Rome", "Naples"),
        ("Rome", "Istanbul"),
    ]

    # Build adjacency set for undirected edges
    direct_edges = {frozenset(pair) for pair in direct_pairs}

    def is_direct(a, b):
        return frozenset((a, b)) in direct_edges

    # Basic feasibility check on durations vs total days with overlaps
    required_sum = sum(durations[c] for c in cities)
    overlaps_needed = len(cities) - 1  # each transition day counts for both cities
    if required_sum != total_days + overlaps_needed:
        result = {"error": "Durations and total days are inconsistent with overlap rule."}
        print(json.dumps(result))
        return

    def compute_schedule(order):
        # Check direct flights adjacency
        for i in range(len(order) - 1):
            if not is_direct(order[i], order[i + 1]):
                return None

        # Build schedule with overlapping transition days:
        # City i occupies [start_i, end_i] where:
        # start_1 = 1, end_i = start_i + duration - 1, and start_{i+1} = end_i
        schedule = {}
        start = 1
        for city in order:
            end = start + durations[city] - 1
            schedule[city] = (start, end)
            start = end  # overlap next start with this end

        # Validate final end equals total_days
        last_city = order[-1]
        if schedule[last_city][1] != total_days:
            return None

        # Validate fixed windows
        for city, (a, b) in fixed_windows.items():
            if city not in schedule or schedule[city] != (a, b):
                return None

        return schedule

    solution = None
    solution_order = None

    # Try all permutations of the 5 cities
    for perm in itertools.permutations(cities):
        schedule = compute_schedule(perm)
        if schedule is not None:
            solution = schedule
            solution_order = perm
            break

    if solution is None:
        result = {"error": "No feasible itinerary found under constraints."}
    else:
        itinerary = []
        for city in solution_order:
            s, e = solution[city]
            itinerary.append({"day_range": f"Day {s}-{e}", "place": city})
        result = {"itinerary": itinerary}

    print(json.dumps(result))

if __name__ == "__main__":
    main()