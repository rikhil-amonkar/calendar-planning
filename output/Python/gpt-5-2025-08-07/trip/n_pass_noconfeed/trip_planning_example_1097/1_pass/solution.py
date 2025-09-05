import itertools
import json

def build_graph():
    graph = {}
    def add_node(u):
        if u not in graph:
            graph[u] = set()
    def add_edge(u, v, bidirectional=True):
        add_node(u); add_node(v)
        graph[u].add(v)
        if bidirectional:
            graph[v].add(u)

    # Cities
    cities = [
        "Reykjavik", "Riga", "Oslo", "Lyon",
        "Dubrovnik", "Madrid", "Warsaw", "London"
    ]

    # Build edges from constraints
    add_edge("Warsaw", "Reykjavik", bidirectional=True)
    add_edge("Oslo", "Madrid", bidirectional=True)
    add_edge("Warsaw", "Riga", bidirectional=True)
    add_edge("Lyon", "London", bidirectional=True)
    add_edge("Madrid", "London", bidirectional=True)
    add_edge("Warsaw", "London", bidirectional=True)
    add_edge("Reykjavik", "Madrid", bidirectional=False)  # one-way
    add_edge("Warsaw", "Oslo", bidirectional=True)
    add_edge("Oslo", "Dubrovnik", bidirectional=True)
    add_edge("Oslo", "Reykjavik", bidirectional=True)
    add_edge("Riga", "Oslo", bidirectional=True)
    add_edge("Oslo", "Lyon", bidirectional=True)
    add_edge("Oslo", "London", bidirectional=True)
    add_edge("London", "Reykjavik", bidirectional=True)
    add_edge("Warsaw", "Madrid", bidirectional=True)
    add_edge("Madrid", "Lyon", bidirectional=True)
    add_edge("Dubrovnik", "Madrid", bidirectional=True)

    # Ensure all cities exist in graph
    for c in cities:
        if c not in graph:
            graph[c] = set()

    return graph

def compute_schedule(order, stays, total_days):
    # Calculate start and end (inclusive) for each city in order with overlap on flight days
    schedule = []
    current_start = 1
    for idx, city in enumerate(order):
        length = stays[city]
        if idx == 0:
            s = current_start
        else:
            s = schedule[-1][2]  # start on previous end (flight day counts for both)
        e = s + length - 1
        schedule.append((city, s, e))
    if schedule[-1][2] != total_days:
        return None  # doesn't fit total days exactly
    return schedule

def interval_contains_any(s, e, days):
    return any(s <= d <= e for d in days)

def find_itinerary(cities, stays, total_days, graph, riga_days, dubrovnik_days):
    n = len(cities)
    # Feasibility check on total days with overlaps: sum(stays) must equal total_days + (n-1)
    if sum(stays[c] for c in cities) != total_days + (n - 1):
        return None

    # Search all permutations for a path that respects direct flights and time windows
    for perm in itertools.permutations(cities):
        # Check direct flights along the permutation
        ok = True
        for i in range(len(perm)-1):
            u, v = perm[i], perm[i+1]
            if v not in graph.get(u, set()):
                ok = False
                break
        if not ok:
            continue

        schedule = compute_schedule(perm, stays, total_days)
        if schedule is None:
            continue

        # Build quick lookup for windows
        city_to_interval = {city: (s, e) for (city, s, e) in schedule}
        s_r, e_r = city_to_interval["Riga"]
        s_d, e_d = city_to_interval["Dubrovnik"]

        if not interval_contains_any(s_r, e_r, set(riga_days)):
            continue
        if not interval_contains_any(s_d, e_d, set(dubrovnik_days)):
            continue

        # Found a valid itinerary
        return schedule

    return None

def format_output(schedule):
    itinerary = []
    for city, s, e in schedule:
        day_range = f"Day {s}-{e}"
        itinerary.append({"day_range": day_range, "place": city})
    return {"itinerary": itinerary}

def main():
    # Input variables
    total_days = 18
    cities = ["Reykjavik", "Riga", "Oslo", "Lyon", "Dubrovnik", "Madrid", "Warsaw", "London"]
    desired_stays = {
        "Reykjavik": 4,
        "Riga": 2,
        "Oslo": 3,
        "Lyon": 5,
        "Dubrovnik": 2,
        "Madrid": 2,
        "Warsaw": 4,
        "London": 3,
    }
    riga_meet_window_days = [4, 5]
    dubrovnik_wedding_window_days = [7, 8]

    graph = build_graph()

    schedule = find_itinerary(
        cities=cities,
        stays=desired_stays,
        total_days=total_days,
        graph=graph,
        riga_days=riga_meet_window_days,
        dubrovnik_days=dubrovnik_wedding_window_days
    )

    if schedule is None:
        output = {"itinerary": [], "status": "no_feasible_itinerary_found"}
    else:
        output = format_output(schedule)

    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()