import json
from constraint import Problem, AllDifferentConstraint

def build_adjacency():
    cities = ["Vienna", "Milan", "Rome", "Riga", "Lisbon", "Vilnius", "Oslo"]

    # Bidirectional edges
    bi_edges = [
        ("Riga", "Oslo"),
        ("Rome", "Oslo"),
        ("Vienna", "Milan"),
        ("Vienna", "Vilnius"),
        ("Vienna", "Lisbon"),
        ("Riga", "Milan"),
        ("Lisbon", "Oslo"),
        ("Rome", "Lisbon"),
        ("Vienna", "Riga"),
        ("Vienna", "Rome"),
        ("Milan", "Oslo"),
        ("Vienna", "Oslo"),
        ("Vilnius", "Oslo"),
        ("Vilnius", "Milan"),
        ("Riga", "Lisbon"),
        ("Milan", "Lisbon"),
    ]
    # Unidirectional edges
    uni_edges = [
        ("Rome", "Riga"),
        ("Riga", "Vilnius"),
    ]

    adj = {c: set() for c in cities}
    for a, b in bi_edges:
        adj[a].add(b)
        adj[b].add(a)
    for a, b in uni_edges:
        adj[a].add(b)
    return adj

def compute_itinerary():
    cities = ["Vienna", "Milan", "Rome", "Riga", "Lisbon", "Vilnius", "Oslo"]

    # Required counted days per city (including flight-day double counts)
    required_counts = {
        "Vienna": 4,
        "Milan": 2,
        "Rome": 3,
        "Riga": 2,
        "Lisbon": 3,
        "Vilnius": 4,
        "Oslo": 3,
    }
    total_days = 15

    # Friend meeting constraint puts Oslo on days 13-15 -> make Oslo the last block
    last_city = "Oslo"

    # Base-length per city (block length without the extra departure-count day)
    base_lengths = {c: (required_counts[c] if c == last_city else required_counts[c] - 1) for c in cities}

    # Sanity check: sum of base lengths must equal total days
    if sum(base_lengths.values()) != total_days:
        raise ValueError("Base lengths do not sum to total days; constraints infeasible.")

    # Build adjacency for direct flights (directed)
    adj = build_adjacency()

    # Use python-constraint to find an order of city blocks that respects direct flights and constraints
    problem = Problem()

    # Position variables for the 7 blocks
    positions = [f"pos{i}" for i in range(1, 8)]

    # Domains
    problem.addVariable("pos1", ["Vienna"])  # Conference day 1 in Vienna
    problem.addVariable("pos7", [last_city])  # Last city must be Oslo (friend days 13-15)
    problem.addVariable("pos6", ["Lisbon"])  # Ensure days 11-13 are in Lisbon (see base length math below)

    middle_cities = set(cities) - {"Vienna", "Lisbon", last_city}
    for i in [2, 3, 4, 5]:
        problem.addVariable(f"pos{i}", list(middle_cities))

    # All cities must be distinct across the 7 blocks
    problem.addConstraint(AllDifferentConstraint(), positions)

    # Only allow direct flights between consecutive blocks
    def edge_allowed(a, b):
        return b in adj[a]

    for i in range(1, 7):
        problem.addConstraint(lambda a, b, ea=edge_allowed: ea(a, b), (f"pos{i}", f"pos{i+1}"))

    solutions = problem.getSolutions()
    if not solutions:
        raise ValueError("No valid itinerary found that satisfies all constraints.")

    # Choose the first solution (any valid solution is acceptable)
    sol = solutions[0]

    # Build base schedule: assign base city for each day according to block order and base lengths
    order = [sol[f"pos{i}"] for i in range(1, 8)]

    # Compute start and end day per block
    block_ranges = []
    cur_day = 1
    for city in order:
        length = base_lengths[city]
        start = cur_day
        end = cur_day + length - 1
        block_ranges.append((city, start, end))
        cur_day = end + 1

    # Build day-by-day base city
    base_city_by_day = {}
    for city, start, end in block_ranges:
        for d in range(start, end + 1):
            base_city_by_day[d] = city

    # Compute "in-city" presence accounting for flight days (change days counted in both cities)
    in_cities_by_day = {d: set() for d in range(1, total_days + 1)}
    for d in range(1, total_days + 1):
        in_cities_by_day[d].add(base_city_by_day[d])
        if d > 1 and base_city_by_day[d] != base_city_by_day[d - 1]:
            # Flight on day d from previous base to current base: both cities count on day d
            in_cities_by_day[d].add(base_city_by_day[d - 1])

    # Validate counted day totals per city
    counted = {c: 0 for c in cities}
    for d in range(1, total_days + 1):
        for c in in_cities_by_day[d]:
            counted[c] += 1

    if counted != required_counts:
        raise ValueError(f"Counted days per city do not match requirements: {counted} vs {required_counts}")

    # Validate key day constraints:
    # - Day 1 and Day 4 in Vienna
    if "Vienna" not in in_cities_by_day[1] or "Vienna" not in in_cities_by_day[4]:
        raise ValueError("Vienna presence on Day 1 and Day 4 is not satisfied.")

    # - Lisbon days 11-13
    for d in [11, 12, 13]:
        if "Lisbon" not in in_cities_by_day[d]:
            raise ValueError("Lisbon presence on Days 11-13 is not satisfied.")

    # - Oslo days 13-15
    for d in [13, 14, 15]:
        if "Oslo" not in in_cities_by_day[d]:
            raise ValueError("Oslo presence on Days 13-15 is not satisfied.")

    # Group into day ranges by "place set" to reflect flight days counting both cities
    itinerary = []
    def place_label(city_set):
        return " & ".join(sorted(city_set))

    start = 1
    current_set = in_cities_by_day[1]
    for d in range(2, total_days + 1):
        if in_cities_by_day[d] != current_set:
            itinerary.append({
                "day_range": f"Day {start}-{d-1}" if d-1 > start else f"Day {start}",
                "place": place_label(current_set)
            })
            start = d
            current_set = in_cities_by_day[d]
    # Append last segment
    itinerary.append({
        "day_range": f"Day {start}-{total_days}" if total_days > start else f"Day {start}",
        "place": place_label(current_set)
    })

    # Output JSON
    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    compute_itinerary()