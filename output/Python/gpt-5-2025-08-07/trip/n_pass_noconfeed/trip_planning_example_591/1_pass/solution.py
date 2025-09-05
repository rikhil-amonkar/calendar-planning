import itertools
import json

def main():
    # Input variables (constraints)
    total_days = 17
    required_stays = {
        "Stuttgart": 2,
        "Bucharest": 2,
        "Geneva": 4,
        "Valencia": 6,
        "Munich": 7,
    }
    direct_flights = [
        ("Geneva", "Munich"),
        ("Munich", "Valencia"),
        ("Bucharest", "Valencia"),
        ("Munich", "Bucharest"),
        ("Valencia", "Stuttgart"),
        ("Geneva", "Valencia"),
    ]
    # Special window constraints (inclusive)
    geneva_relatives_window = (1, 4)   # Must be in Geneva on these days
    munich_friends_window = (4, 10)    # Must be in Munich on at least one of these days

    cities = list(required_stays.keys())
    sum_required_days = sum(required_stays.values())
    flights_needed = sum_required_days - total_days  # Each flight day counts twice (departure and arrival)
    if flights_needed < 0:
        raise ValueError("Impossible constraints: total required days less than total trip days.")
    if flights_needed > len(cities) - 1:
        raise ValueError("Impossible constraints: too many overlapping days required for available city blocks.")

    # Build adjacency set for quick lookup (undirected)
    edges = set()
    for a, b in direct_flights:
        edges.add((a, b))
        edges.add((b, a))

    def connected_path(order):
        return all((order[i], order[i+1]) in edges for i in range(len(order)-1))

    def compute_schedule(order):
        # Given a city order and required stays, compute inclusive [start, end] days per city
        schedule = {}
        current_start = 1
        for city in order:
            dur = required_stays[city]
            start = current_start
            end = start + dur - 1
            schedule[city] = (start, end)
            # Next city begins on the same day as end due to flight-day overlap rule
            current_start = end
        total_span = schedule[order[-1]][1]
        return schedule, total_span

    def interval_intersects(a, b, c, d):
        return max(a, c) <= min(b, d)

    def interval_contains(a, b, c, d):
        # [a,b] contains [c,d]
        return a <= c and b >= d

    feasible_plans = []
    # Iterate permutations to find Hamiltonian paths that satisfy constraints
    for order in itertools.permutations(cities):
        # Must use exactly len(cities)-1 flights if each city is visited once
        if flights_needed != len(order) - 1:
            continue
        # Must be a valid path with only direct flights
        if not connected_path(order):
            continue
        # Compute schedule and validate total days
        schedule, span = compute_schedule(order)
        if span != total_days:
            continue
        # Geneva relatives window: we must be in Geneva on all days 1-4 (since Geneva stay is exactly 4 days)
        if "Geneva" not in schedule:
            continue
        g_start, g_end = schedule["Geneva"]
        if not interval_contains(g_start, g_end, geneva_relatives_window[0], geneva_relatives_window[1]):
            continue
        # Munich friends window: at least one day overlap between Munich and [4,10]
        if "Munich" not in schedule:
            continue
        m_start, m_end = schedule["Munich"]
        if not interval_intersects(m_start, m_end, munich_friends_window[0], munich_friends_window[1]):
            continue

        # Candidate passed all constraints; create sorting key to choose an "optimal" one
        # Preference: earliest Munich start (more overlap with friends' window), then lexicographic order
        feasible_plans.append((order, schedule, (m_start, tuple(order))))

    if not feasible_plans:
        # If no plan found, output empty itinerary
        print(json.dumps({"itinerary": []}, ensure_ascii=False))
        return

    # Choose optimal candidate per defined preference
    feasible_plans.sort(key=lambda x: x[2])
    best_order, best_schedule, _ = feasible_plans[0]

    # Build itinerary as list of {"day_range": "Day X-Y", "place": City}
    itinerary = []
    for city in best_order:
        s, e = best_schedule[city]
        itinerary.append({"day_range": f"Day {s}-{e}", "place": city})

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()