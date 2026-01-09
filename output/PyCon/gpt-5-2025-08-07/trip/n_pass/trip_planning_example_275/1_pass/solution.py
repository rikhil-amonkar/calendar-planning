import json
from constraint import Problem

def find_hamiltonian_paths_end_at(nodes, edges, end_city):
    # Undirected graph adjacency
    adj = {n: set() for n in nodes}
    for a, b in edges:
        adj[a].add(b)
        adj[b].add(a)

    paths = []

    def dfs(path, visited):
        if len(path) == len(nodes):
            if path[-1] == end_city:
                paths.append(path[:])
            return
        last = path[-1]
        for nb in adj[last]:
            if nb not in visited:
                visited.add(nb)
                path.append(nb)
                dfs(path, visited)
                path.pop()
                visited.remove(nb)

    for start in nodes:
        if start == end_city:
            continue  # cannot end at end_city if we start there unless graph cycles, which it doesn't here
        dfs([start], {start})
    return paths

def main():
    # Input constraints
    total_days = 14
    required_days = {
        "Vilnius": 4,
        "Split": 5,
        "Madrid": 6,
        "Santorini": 2,
    }
    conference_city = "Santorini"
    conference_days = [13, 14]
    direct_flights = [
        ("Vilnius", "Split"),
        ("Split", "Madrid"),
        ("Madrid", "Santorini"),
    ]

    cities = list(required_days.keys())

    # Compute valid visiting order(s) using direct flights; must end at conference city
    orders = find_hamiltonian_paths_end_at(cities, direct_flights, conference_city)
    if not orders:
        raise RuntimeError("No valid city order that respects direct flights and ends at the conference city.")

    # Filter orders so that conference days can be satisfied with the given duration in the last city
    valid_orders = []
    for order in orders:
        if order[-1] != conference_city:
            continue
        # With inclusive days and overlaps on flight days:
        # starting day for first city will be constrained to 1,
        # so Santorini will start at total_days - required_days['Santorini'] + 1 to include day 14,
        # but must also include day 13 within its span.
        # Given duration = 2, that means start day must be 13 exactly.
        # This is feasible, so keep this order.
        valid_orders.append(order)

    if not valid_orders:
        raise RuntimeError("No visiting order can satisfy the conference-day requirement.")

    # Choose the first valid order (unique for this graph)
    order = valid_orders[0]

    # Set up CSP with python-constraint
    problem = Problem()

    # Variables: start day for each city (inclusive)
    # Domain limited so that end day doesn't exceed total_days
    start_vars = {}
    for city in cities:
        max_start = total_days - required_days[city] + 1
        domain = range(1, max_start + 1)
        start_vars[city] = f"s_{city}"
        problem.addVariable(start_vars[city], domain)

    # 1) Trip starts on Day 1 at the first city in the order
    problem.addConstraint(lambda s: s == 1, (start_vars[order[0]],))

    # 2) Enforce overlaps on flight days between consecutive cities (direct flights)
    #    If flying from A to B on day X, then:
    #    start_B == end_A == start_A + dur_A - 1
    for i in range(len(order) - 1):
        a, b = order[i], order[i + 1]
        dur_a = required_days[a]
        problem.addConstraint(
            lambda sa, sb, da=dur_a: sb == sa + da - 1,
            (start_vars[a], start_vars[b])
        )

    # 3) Conference: must be in Santorini on Day 13 and Day 14
    #    With inclusive days and duration 2, this implies start_santorini == 13
    problem.addConstraint(lambda s: s == conference_days[0], (start_vars[conference_city],))
    # Also ensure Santorini ends on Day 14
    problem.addConstraint(
        lambda s, d=required_days[conference_city]: s + d - 1 == conference_days[-1],
        (start_vars[conference_city],)
    )

    # Solve
    solutions = problem.getSolutions()
    if not solutions:
        raise RuntimeError("No feasible itinerary found under the given constraints.")

    sol = solutions[0]

    # Build itinerary with inclusive ranges; flight days overlap between consecutive cities
    itinerary = []
    for city in order:
        start = sol[start_vars[city]]
        end = start + required_days[city] - 1
        itinerary.append({
            "day_range": f"Day {start}-{end}",
            "place": city
        })

    # Optional validation: compute unique trip days and city-day counts
    # Ensure union of days equals total_days and city counts match required_days
    city_days = {c: set(range(sol[start_vars[c]], sol[start_vars[c]] + required_days[c])) for c in cities}
    total_unique_days = set()
    for c in cities:
        total_unique_days.update(city_days[c])
    assert min(total_unique_days) == 1 and max(total_unique_days) == total_days and len(total_unique_days) == total_days
    for c in cities:
        assert len(city_days[c]) == required_days[c]
    # Ensure adjacency used is direct flights
    for i in range(len(order) - 1):
        a, b = order[i], order[i + 1]
        assert (a, b) in direct_flights or (b, a) in direct_flights

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()