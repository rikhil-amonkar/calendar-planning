import json
from collections import defaultdict

def build_adjacency(edges, cities):
    adj = {c: set() for c in cities}
    for a, b in edges:
        if a in adj and b in adj:
            adj[a].add(b)
            adj[b].add(a)
    return adj

def compute_start_end(order, durations):
    # With shared boundary days, the start day of k-th city:
    # start_day = 1 + sum_{i < k}(durations[i] - 1)
    schedule = {}
    sum_dm1 = 0
    for city in order:
        start = 1 + sum_dm1
        end = start + durations[city] - 1
        schedule[city] = (start, end)
        sum_dm1 += (durations[city] - 1)
    return schedule

def satisfies_constraints(schedule, constraints):
    # Mykonos must include days 10 and 11
    s, e = schedule["Mykonos"]
    if not (s <= 10 <= e and s <= 11 <= e):
        return False
    # Seville must cover days 13..17 (duration 5 -> exactly 13-17)
    s, e = schedule["Seville"]
    if not (s == 13 and e == 17):
        return False
    # Frankfurt wedding between day 1 and 5 (must intersect)
    s, e = schedule["Frankfurt"]
    if e < 1 or s > 5:
        return False
    return True

def find_itinerary(cities, durations, edges):
    adj = build_adjacency(edges, cities)

    # Targets derived from fixed dates with shared-boundary scheme:
    # start_day(city) = 1 + sum_prev(d_i - 1)
    # Mykonos must start at day 10 -> sum_prev = 9
    # Seville must start at day 13 -> sum_prev = 12
    target_sum_before = {"Mykonos": 9, "Seville": 12}

    # Backtracking search. Fix Frankfurt first to satisfy the wedding window easily.
    start_city = "Frankfurt"
    remaining = [c for c in cities if c != start_city]

    # A heuristic priority to reach a feasible solution quickly
    priority_order = ["Venice", "Nice", "Mykonos", "Rome", "Seville", "Dublin", "Bucharest", "Lisbon", "Stuttgart"]
    priority = {name: i for i, name in enumerate(priority_order)}

    best_order = None

    def backtrack(order, used, sum_dm1, schedule):
        nonlocal best_order
        if len(order) == len(cities):
            # Verify adjacency for last is already checked; now verify constraints
            if satisfies_constraints(schedule, None):
                best_order = order[:]
            return

        prev = order[-1]
        # Candidates sorted by heuristic priority
        candidates = sorted((c for c in cities if c not in used), key=lambda x: priority.get(x, 999))

        for city in candidates:
            # Adjacency (direct flight) required
            if city not in adj[prev]:
                continue

            # Start and end day for this city if placed now
            start_day = 1 + sum_dm1
            end_day = start_day + durations[city] - 1

            # Enforce fixed-date exact starts for Mykonos and Seville
            if city in target_sum_before and sum_dm1 != target_sum_before[city]:
                continue

            # Prune if we have already passed the required sum for a future fixed city
            # If we haven't placed Mykonos yet and sum_dm1 > 9, impossible
            if "Mykonos" not in schedule and city != "Mykonos" and sum_dm1 > target_sum_before["Mykonos"]:
                continue
            # If we haven't placed Seville yet and sum_dm1 > 12, impossible
            if "Seville" not in schedule and city != "Seville" and sum_dm1 > target_sum_before["Seville"]:
                continue

            # Prune if placing this city jumps over the exact sum needed for fixed cities
            new_sum = sum_dm1 + (durations[city] - 1)
            if "Mykonos" not in schedule and city != "Mykonos":
                if sum_dm1 < target_sum_before["Mykonos"] < new_sum:
                    continue
            if "Seville" not in schedule and city != "Seville":
                if sum_dm1 < target_sum_before["Seville"] < new_sum:
                    continue

            # Tentatively place city
            used.add(city)
            order.append(city)
            schedule[city] = (start_day, end_day)

            backtrack(order, used, new_sum, schedule)
            if best_order is not None:
                return  # Found a feasible itinerary

            # Undo
            used.remove(city)
            order.pop()
            del schedule[city]

    initial_order = [start_city]
    initial_used = {start_city}
    initial_schedule = {start_city: (1, 1 + durations[start_city] - 1)}
    initial_sum_dm1 = durations[start_city] - 1

    backtrack(initial_order, initial_used, initial_sum_dm1, initial_schedule)

    if best_order is None:
        return None

    # Build full schedule and itinerary output
    schedule = compute_start_end(best_order, durations)
    itinerary = []
    for city in best_order:
        s, e = schedule[city]
        itinerary.append({"day_range": f"Day {s}-{e}", "place": city})
    return {"itinerary": itinerary}

def main():
    # Input variables (constraints and data)
    durations = {
        "Rome": 3,
        "Mykonos": 2,
        "Lisbon": 2,
        "Frankfurt": 5,
        "Nice": 3,
        "Stuttgart": 4,
        "Venice": 4,
        "Dublin": 2,
        "Bucharest": 2,
        "Seville": 5,
    }
    cities = list(durations.keys())

    # Direct flight edges (undirected)
    edges = [
        ("Rome", "Stuttgart"),
        ("Venice", "Rome"),
        ("Dublin", "Bucharest"),
        ("Mykonos", "Rome"),
        ("Seville", "Lisbon"),
        ("Frankfurt", "Venice"),
        ("Venice", "Stuttgart"),
        ("Bucharest", "Lisbon"),
        ("Nice", "Mykonos"),
        ("Venice", "Lisbon"),
        ("Dublin", "Lisbon"),
        ("Venice", "Dublin"),
        ("Venice", "Nice"),
        ("Rome", "Seville"),
        ("Frankfurt", "Rome"),
        ("Nice", "Dublin"),
        ("Rome", "Bucharest"),
        ("Frankfurt", "Dublin"),
        ("Rome", "Dublin"),
        ("Venice", "Dublin"),
        ("Rome", "Lisbon"),
        ("Frankfurt", "Lisbon"),
        ("Nice", "Rome"),
        ("Frankfurt", "Nice"),
        ("Frankfurt", "Stuttgart"),
        ("Frankfurt", "Bucharest"),
        ("Lisbon", "Stuttgart"),
        ("Nice", "Lisbon"),
        ("Seville", "Dublin"),
    ]

    result = find_itinerary(cities, durations, edges)
    if result is None:
        print(json.dumps({"error": "No feasible itinerary found that satisfies all constraints."}))
    else:
        print(json.dumps(result))

if __name__ == "__main__":
    main()