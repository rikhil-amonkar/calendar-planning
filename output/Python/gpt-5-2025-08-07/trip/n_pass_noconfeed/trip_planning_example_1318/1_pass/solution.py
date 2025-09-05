import json
from collections import defaultdict

def build_adjacency(cities, flight_descriptions):
    adj = {city: set() for city in cities}
    # Parse flight descriptions: "A and B" means bidirectional; "from A to B" means A->B only.
    for desc in flight_descriptions:
        desc = desc.strip()
        if desc.startswith("from "):
            # format: from X to Y
            rest = desc[len("from "):]
            parts = rest.split(" to ")
            if len(parts) == 2:
                a = parts[0].strip()
                b = parts[1].strip()
                if a in adj and b in adj:
                    adj[a].add(b)
        else:
            # format: A and B
            parts = desc.split(" and ")
            if len(parts) == 2:
                a = parts[0].strip()
                b = parts[1].strip()
                if a in adj and b in adj:
                    adj[a].add(b)
                    adj[b].add(a)
    return adj

def compute_schedule(order, durations):
    itinerary = []
    day_starts = {}
    day_ends = {}
    if not order:
        return itinerary, day_starts, day_ends
    current_start = 1
    for i, city in enumerate(order):
        dur = durations[city]
        start = current_start
        end = start + dur - 1
        day_starts[city] = start
        day_ends[city] = end
        itinerary.append({"day_range": f"Day {start}-{end}", "place": city})
        # Overlap travel day rule: next city starts on the same day the previous ended
        current_start = end
    return itinerary, day_starts, day_ends

def intersects(range_a, range_b):
    a1, a2 = range_a
    b1, b2 = range_b
    return not (a2 < b1 or b2 < a1)

def find_itinerary(cities, durations, flights, total_days, window_constraints, last_city):
    adj = build_adjacency(cities, flights)

    # Quick feasibility checks
    if sum(durations.values()) - (len(cities) - 1) != total_days:
        return None  # impossible to fit total days under the overlap rule

    # Precompute d-1 for pruning
    d_minus_1 = {c: durations[c] - 1 for c in cities}
    target_city = None
    target_window = None
    if "Tallinn" in window_constraints:
        target_city = "Tallinn"
        target_window = window_constraints["Tallinn"]

    best_order = None  # we just need a feasible one; "optimal" under constraints is a valid solution

    rest_cities = [c for c in cities if c != last_city]

    def dfs(path, used):
        nonlocal best_order

        if best_order is not None:
            return

        # Prune: if Tallinn not yet in path, and even placing it next will start after its window
        if target_city and target_city not in path:
            sum_dminus1_so_far = sum(d_minus_1[c] for c in path)
            earliest_start_if_next = 1 + sum_dminus1_so_far
            if earliest_start_if_next > target_window[1]:
                return

        if len(path) == 0:
            # Try all possible starting cities except the fixed last city
            for city in sorted(rest_cities):
                dfs([city], {city})
            return

        # If path is complete (all but last city), try to append last city if direct flight exists
        if len(path) == len(cities) - 1:
            prev = path[-1]
            if last_city in adj.get(prev, set()):
                candidate_order = path + [last_city]
                # Validate full itinerary
                itinerary, starts, ends = compute_schedule(candidate_order, durations)
                # Check total-day end
                if itinerary and "place" in itinerary[-1]:
                    total_end_day = int(itinerary[-1]["day_range"].split("-")[1])
                    if total_end_day != total_days:
                        return
                # Check Tallinn window (wedding) if applicable
                if target_city:
                    if not intersects((starts[target_city], ends[target_city]), target_window):
                        return
                # Check friend in Oslo window (should be satisfied if Oslo is last with 2 days)
                if "Oslo" in window_constraints:
                    oslo_window = window_constraints["Oslo"]
                    if not intersects((starts["Oslo"], ends["Oslo"]), oslo_window):
                        return
                best_order = candidate_order
            return

        # Otherwise expand by choosing a neighbor of the last city
        last = path[-1]
        for nxt in sorted(adj.get(last, set())):
            if nxt in used:
                continue
            if nxt == last_city:
                # reserve last city for the very end
                continue
            # Extend path
            new_path = path + [nxt]
            new_used = set(used)
            new_used.add(nxt)

            # Prune adjacency that makes completion impossible: ensure remaining cities are reachable in some way?
            # We'll rely on adjacency checks and final validation.

            # If Tallinn is placed now, check its window immediately
            if target_city and nxt == target_city:
                # Compute start for Tallinn given new_path
                _, starts, ends = compute_schedule(new_path, durations)
                if starts[target_city] > window_constraints[target_city][1]:
                    continue  # too late to catch the window

            dfs(new_path, new_used)

    dfs([], set())
    if best_order is None:
        return None

    itinerary, starts, ends = compute_schedule(best_order, durations)
    return itinerary

def main():
    total_days = 25

    # City durations (days spent in each city)
    durations = {
        "Oslo": 2,
        "Helsinki": 2,
        "Edinburgh": 3,
        "Riga": 2,
        "Tallinn": 5,
        "Budapest": 5,
        "Vilnius": 5,
        "Porto": 5,
        "Geneva": 4,
    }
    cities = list(durations.keys())

    # Flight descriptions as provided
    flight_descriptions = [
        "Porto and Oslo",
        "Edinburgh and Budapest",
        "Edinburgh and Geneva",
        "from Riga to Tallinn",
        "Edinburgh and Porto",
        "Vilnius and Helsinki",
        "from Tallinn to Vilnius",
        "Riga and Oslo",
        "Geneva and Oslo",
        "Edinburgh and Oslo",
        "Edinburgh and Helsinki",
        "Vilnius and Oslo",
        "Riga and Helsinki",
        "Budapest and Geneva",
        "Helsinki and Budapest",
        "Helsinki and Oslo",
        "Edinburgh and Riga",
        "Tallinn and Helsinki",
        "Geneva and Porto",
        "Budapest and Oslo",
        "Helsinki and Geneva",
        "from Riga to Vilnius",
        "Tallinn and Oslo",
    ]

    # Constraints:
    # - Wedding in Tallinn between day 4 and day 8 (inclusive)
    # - Meet friend in Oslo between day 24 and day 25 (inclusive)
    window_constraints = {
        "Tallinn": (4, 8),
        "Oslo": (24, 25),
    }

    # Fix last city to Oslo to meet the friend window naturally (with 2-day stay)
    last_city = "Oslo"

    itinerary = find_itinerary(cities, durations, flight_descriptions, total_days, window_constraints, last_city)

    if itinerary is None:
        # Fallback: no solution found (should not happen with given data)
        output = {"error": "No feasible itinerary found with the given constraints."}
    else:
        output = {"itinerary": itinerary}

    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()