import json
from collections import defaultdict

def build_graph():
    edges = defaultdict(set)

    def add_bidir(a, b):
        edges[a].add(b)
        edges[b].add(a)

    def add_dir(a, b):
        edges[a].add(b)

    # Bidirectional edges
    add_bidir("Munich", "Vienna")
    add_bidir("Istanbul", "Brussels")
    add_bidir("Vienna", "Vilnius")
    add_bidir("Madrid", "Munich")
    add_bidir("Venice", "Brussels")
    add_bidir("Riga", "Brussels")
    add_bidir("Geneva", "Istanbul")
    add_bidir("Munich", "Reykjavik")
    add_bidir("Vienna", "Istanbul")
    add_bidir("Riga", "Istanbul")
    add_bidir("Reykjavik", "Vienna")
    add_bidir("Venice", "Munich")
    add_bidir("Madrid", "Venice")
    add_bidir("Vilnius", "Istanbul")
    add_bidir("Venice", "Vienna")
    add_bidir("Venice", "Istanbul")
    add_bidir("Reykjavik", "Brussels")
    add_bidir("Vilnius", "Brussels")
    add_bidir("Madrid", "Vienna")
    add_bidir("Vienna", "Riga")
    add_bidir("Geneva", "Vienna")
    add_bidir("Madrid", "Brussels")
    add_bidir("Vienna", "Brussels")
    add_bidir("Geneva", "Brussels")
    add_bidir("Geneva", "Madrid")
    add_bidir("Munich", "Brussels")
    add_bidir("Madrid", "Istanbul")
    add_bidir("Geneva", "Munich")
    add_bidir("Munich", "Istanbul")

    # Directed edges
    add_dir("Reykjavik", "Madrid")
    add_dir("Riga", "Munich")
    add_dir("Vilnius", "Munich")
    add_dir("Riga", "Vilnius")

    return edges

def compute_itinerary():
    # Trip constraints
    durations = {
        "Istanbul": 4,
        "Vienna": 4,
        "Riga": 2,
        "Brussels": 2,
        "Madrid": 4,
        "Vilnius": 4,
        "Venice": 5,
        "Geneva": 4,
        "Munich": 5,
        "Reykjavik": 2,
    }

    must_cover = {
        # city: (start_day_required, end_day_required), inclusive
        "Geneva": (1, 4),
        "Venice": (7, 11),
        "Vilnius": (20, 23),
        "Brussels": (26, 27),
    }

    total_days = 27
    cities = list(durations.keys())
    start_city = "Geneva"
    end_city = "Brussels"

    edges = build_graph()

    # Basic sanity check on durations vs total days with overlaps
    sum_durations = sum(durations.values())
    n_transitions = len(cities) - 1
    assert sum_durations - n_transitions == total_days, "Durations mismatch for 27-day plan with 10 cities."

    # DFS with pruning
    remaining = set(cities)
    remaining.remove(start_city)
    remaining.remove(end_city)  # reserve end city as last

    # schedule entries are tuples: (city, start_day, end_day)
    schedule = [(start_city, 1, 1 + durations[start_city] - 1)]

    # Verify start city must_cover
    s0, e0 = schedule[0][1], schedule[0][2]
    req_s, req_e = must_cover[start_city]
    if not (s0 <= req_s and e0 >= req_e):
        raise ValueError("Start city must-cover constraint violated.")

    # Helper: feasibility prune for future must-cover cities
    def future_windows_still_possible(current_end, placed_set):
        for city, (ws, we) in must_cover.items():
            if city in placed_set:
                continue
            if city == end_city:
                # Brussels is last; it will always be placed at the end with s=26,e=27
                continue
            # If we've already advanced beyond the required start day for a not-yet-placed must city, impossible.
            if current_end > ws:
                return False
        return True

    solution = None

    # To keep search deterministic and efficient, sort remaining candidates alphabetically
    ordered_remaining = sorted(list(remaining))

    def dfs(path, sched, rem):
        nonlocal solution
        if solution is not None:
            return

        current_city = path[-1]
        current_end = sched[-1][2]

        # Prune if future must windows cannot be met anymore
        placed = set([c for c, _, _ in sched])
        if not future_windows_still_possible(current_end, placed):
            return

        if not rem:
            # Place the end city if edge exists
            if end_city in edges[current_city]:
                s = current_end
                e = s + durations[end_city] - 1
                # Validate must_cover for end city
                if end_city in must_cover:
                    ws, we = must_cover[end_city]
                    if not (s <= ws and e >= we):
                        return
                full_schedule = sched + [(end_city, s, e)]
                # Validate final day equals 27
                if full_schedule[-1][2] != 27:
                    return
                solution = full_schedule
            return

        for candidate in rem:
            if candidate not in edges[current_city]:
                continue
            s = current_end
            e = s + durations[candidate] - 1

            # Check candidate's must-cover if any
            if candidate in must_cover:
                ws, we = must_cover[candidate]
                if not (s <= ws and e >= we):
                    continue

            next_path = path + [candidate]
            next_sched = sched + [(candidate, s, e)]
            next_rem = rem.copy()
            next_rem.remove(candidate)
            dfs(next_path, next_sched, next_rem)
            if solution is not None:
                return

    dfs([start_city], schedule, set(ordered_remaining))

    if solution is None:
        raise RuntimeError("No valid itinerary found under the given constraints.")

    # Build JSON-ready itinerary with "Day X-Y" and "place"
    itinerary = []
    for city, s, e in solution:
        itinerary.append({
            "day_range": f"Day {s}-{e}",
            "place": city
        })

    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = compute_itinerary()
    print(json.dumps(result, ensure_ascii=False))