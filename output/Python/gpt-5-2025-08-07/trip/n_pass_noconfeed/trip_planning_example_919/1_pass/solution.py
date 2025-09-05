import json
from itertools import permutations

def build_graph():
    graph = {}
    def add_node(a):
        if a not in graph:
            graph[a] = set()
    def add_bidirectional(a, b):
        add_node(a); add_node(b)
        graph[a].add(b)
        graph[b].add(a)
    def add_directed(a, b):
        add_node(a); add_node(b)
        graph[a].add(b)

    # Build flight graph based on provided direct flights
    add_bidirectional("Riga", "Oslo")
    add_bidirectional("Rome", "Oslo")
    add_bidirectional("Vienna", "Milan")
    add_bidirectional("Vienna", "Vilnius")
    add_bidirectional("Vienna", "Lisbon")
    add_bidirectional("Riga", "Milan")
    add_bidirectional("Lisbon", "Oslo")
    add_directed("Rome", "Riga")
    add_bidirectional("Rome", "Lisbon")
    add_bidirectional("Vienna", "Riga")
    add_bidirectional("Vienna", "Rome")
    add_bidirectional("Milan", "Oslo")
    add_bidirectional("Vienna", "Oslo")
    add_bidirectional("Vilnius", "Oslo")
    add_directed("Riga", "Vilnius")
    add_bidirectional("Vilnius", "Milan")
    add_bidirectional("Riga", "Lisbon")
    add_bidirectional("Milan", "Lisbon")
    return graph

def compute_schedule(order, durations, start_day=1):
    # Returns dict: city -> (start_day, end_day), and final end day
    schedule = {}
    s = start_day
    for i, city in enumerate(order):
        d = durations[city]
        e = s + d - 1
        schedule[city] = (s, e)
        if i < len(order) - 1:
            s = e  # flight on end day overlaps next city's start
    final_end = e
    return schedule, final_end

def valid_edges(order, graph):
    return all(order[i+1] in graph.get(order[i], set()) for i in range(len(order)-1))

def day_in_city(day, city, schedule):
    s, e = schedule[city]
    return s <= day <= e

def main():
    total_days = 15

    # Required days per city
    durations = {
        "Vienna": 4,
        "Milan": 2,
        "Rome": 3,
        "Riga": 2,
        "Lisbon": 3,
        "Vilnius": 4,
        "Oslo": 3,
    }

    # Special constraints
    must_be_in_vienna_days = [1, 4]
    lisbon_window = (11, 13)  # inclusive
    oslo_window = (13, 15)    # inclusive

    cities = list(durations.keys())
    graph = build_graph()

    # We will construct an order that starts in Vienna and ends in Oslo,
    # with Lisbon immediately before Oslo to satisfy Lisbon 11-13 and Oslo 13-15.
    start_city = "Vienna"
    end_city = "Oslo"
    fixed_tail = ["Lisbon", "Oslo"]

    intermediates = [c for c in cities if c not in {start_city} | set(fixed_tail)]

    found_solution = None

    for perm in permutations(intermediates):
        order = [start_city] + list(perm) + fixed_tail

        # Check direct flights feasibility between consecutive cities
        if not valid_edges(order, graph):
            continue

        # Compute schedule
        schedule, final_end = compute_schedule(order, durations, start_day=1)

        # Check final day matches total_days
        if final_end != total_days:
            continue

        # Check Vienna contains day 1 and day 4
        if not all(day_in_city(d, "Vienna", schedule) for d in must_be_in_vienna_days):
            continue

        # Check Lisbon exactly covers days 11-13 (and equals its duration)
        lis_s, lis_e = schedule["Lisbon"]
        if not (lis_s <= lisbon_window[0] and lis_e >= lisbon_window[1]):
            continue
        # Since Lisbon duration is 3, to cover 11-13 it must be exactly 11-13
        if not (lis_s == 11 and lis_e == 13):
            continue

        # Check Oslo covers 13-15
        osl_s, osl_e = schedule["Oslo"]
        if not (oslo_window[0] >= osl_s and oslo_window[1] <= osl_e):
            continue

        # Sanity: verify each city's credited days equal durations
        ok_durations = all((schedule[c][1] - schedule[c][0] + 1) == durations[c] for c in cities)
        if not ok_durations:
            continue

        found_solution = (order, schedule)
        break

    if not found_solution:
        # If no solution found, output empty itinerary to adhere to spec
        result = {"itinerary": []}
        print(json.dumps(result, ensure_ascii=False))
        return

    order, schedule = found_solution

    # Build itinerary output: list of day ranges for each city in order
    itinerary = []
    for city in order:
        s, e = schedule[city]
        itinerary.append({
            "day_range": f"Day {s}-{e}",
            "place": city
        })

    result = {"itinerary": itinerary}
    print(json.dumps(result, ensure_ascii=False))

if __name__ == "__main__":
    main()