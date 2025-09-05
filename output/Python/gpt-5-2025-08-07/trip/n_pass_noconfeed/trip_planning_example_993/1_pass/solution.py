import json
from itertools import permutations, product

def build_flight_graph(edges):
    graph = {}
    for e in edges:
        if e["type"] == "undirected":
            a, b = e["a"], e["b"]
            graph.setdefault(a, set()).add(b)
            graph.setdefault(b, set()).add(a)
        elif e["type"] == "directed":
            a, b = e["a"], e["b"]
            graph.setdefault(a, set()).add(b)
            graph.setdefault(b, set())  # ensure node exists
        else:
            raise ValueError("Unknown edge type")
    return graph

def find_itinerary(cities, durations, total_days, fixed_starts, graph, start_day=1):
    n = len(cities)
    # Backtracking over ordered sequences with dynamic start day computations

    # Pre-calc: we must use overlap rule: next.start = current.end
    # Duration coverage property ensures end_last = start_day + sum(durations) - (n-1) - 1
    if start_day + sum(durations[c] for c in cities) - (n - 1) - 1 != total_days:
        # If this invariant fails, no solution exists with full overlap at each transition
        return None

    # Helper to prune if current timeline makes some fixed start impossible
    def violates_future_fixed(current_end, placed_set):
        for city, s in fixed_starts.items():
            if city not in placed_set and current_end > s:
                return True
        return False

    best_solution = None  # we'll stop at first valid

    # Candidate starting cities exclude those with a fixed start different from start_day
    start_candidates = [c for c in cities if fixed_starts.get(c, start_day) == start_day]

    # If no city explicitly fixed to start_day, allow any city without fixed start constraint
    if not start_candidates:
        start_candidates = [c for c in cities if c not in fixed_starts]

    # For determinism, sort candidates
    start_candidates = sorted(start_candidates)

    def backtrack(sequence, starts, used):
        nonlocal best_solution
        if best_solution is not None:
            return  # already found

        if len(sequence) == 0:
            # choose starting city
            for c0 in start_candidates:
                s0 = start_day
                # respect fixed start if exists
                if fixed_starts.get(c0, s0) != s0:
                    continue
                e0 = s0 + durations[c0] - 1
                if violates_future_fixed(e0, used | {c0}):
                    continue
                backtrack([c0], {c0: s0}, used | {c0})
            return

        if len(sequence) == n:
            # all cities placed; validate end equals total_days
            last_city = sequence[-1]
            end_last = starts[last_city] + durations[last_city] - 1
            if end_last == total_days:
                # Ensure all fixed starts are matched
                for city, s in fixed_starts.items():
                    if starts.get(city) != s:
                        return
                best_solution = (sequence, starts)
            return

        prev = sequence[-1]
        prev_end = starts[prev] + durations[prev] - 1

        # Next city must be not used, have direct flight from prev, and respect fixed start if any
        candidates = [c for c in cities if c not in used and c in graph.get(prev, set())]

        # Sort for determinism
        candidates.sort()

        for c in candidates:
            s = prev_end  # overlap flight day
            # Respect fixed start
            if fixed_starts.get(c, s) != s:
                continue
            e = s + durations[c] - 1
            # Bound check
            if e > total_days:
                continue
            # Future fixed feasibility
            if violates_future_fixed(e, used | {c}):
                continue
            backtrack(sequence + [c], {**starts, c: s}, used | {c})

    backtrack([], {}, set())
    return best_solution

def main():
    # Input variables (constraints)
    total_days = 15
    cities = [
        "Riga",
        "Frankfurt",
        "Amsterdam",
        "Vilnius",
        "London",
        "Stockholm",
        "Bucharest",
    ]
    durations = {
        "Riga": 2,
        "Frankfurt": 3,
        "Amsterdam": 2,   # Must include days 2 and 3 (meeting)
        "Vilnius": 5,     # Workshop between days 7 and 11
        "London": 2,
        "Stockholm": 3,   # Wedding between days 13 and 15
        "Bucharest": 4,
    }
    # Fixed start days derived from event windows:
    # Amsterdam must cover days 2-3 with duration 2 -> start at 2
    # Vilnius must cover days 7-11 with duration 5 -> start at 7
    # Stockholm must cover days 13-15 with duration 3 -> start at 13
    fixed_starts = {
        "Amsterdam": 2,
        "Vilnius": 7,
        "Stockholm": 13,
    }

    # Flight connectivity (direct flights only)
    edges = [
        {"type": "undirected", "a": "London", "b": "Amsterdam"},
        {"type": "undirected", "a": "Vilnius", "b": "Frankfurt"},
        {"type": "directed",   "a": "Riga", "b": "Vilnius"},
        {"type": "undirected", "a": "Riga", "b": "Stockholm"},
        {"type": "undirected", "a": "London", "b": "Bucharest"},
        {"type": "undirected", "a": "Amsterdam", "b": "Stockholm"},
        {"type": "undirected", "a": "Amsterdam", "b": "Frankfurt"},
        {"type": "undirected", "a": "Frankfurt", "b": "Stockholm"},
        {"type": "undirected", "a": "Bucharest", "b": "Riga"},
        {"type": "undirected", "a": "Amsterdam", "b": "Riga"},
        {"type": "undirected", "a": "Amsterdam", "b": "Bucharest"},
        {"type": "undirected", "a": "Riga", "b": "Frankfurt"},
        {"type": "undirected", "a": "Bucharest", "b": "Frankfurt"},
        {"type": "undirected", "a": "London", "b": "Frankfurt"},
        {"type": "undirected", "a": "London", "b": "Stockholm"},
        {"type": "undirected", "a": "Amsterdam", "b": "Vilnius"},
    ]
    graph = build_flight_graph(edges)

    solution = find_itinerary(cities, durations, total_days, fixed_starts, graph, start_day=1)
    if solution is None:
        print(json.dumps({"itinerary": []}))
        return

    sequence, starts = solution

    # Build readable itinerary sorted by start day
    items = []
    for city in sequence:
        s = starts[city]
        e = s + durations[city] - 1
        items.append({"day_range": f"Day {s}-{e}", "place": city})

    output = {"itinerary": items}
    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()