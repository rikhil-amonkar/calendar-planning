import json
from z3 import *

def solve_itinerary():
    # Define cities and IDs
    cities = ["Istanbul", "Rome", "Seville", "Naples", "Santorini"]
    city_id = {name: idx for idx, name in enumerate(cities)}
    IST, ROM, SEV, NAP, SAN = [city_id[name] for name in cities]

    # Trip parameters
    total_days = 16

    # Desired durations per city (days count includes overlap on flight days)
    durations = {
        IST: 2,
        ROM: 3,
        SEV: 4,
        NAP: 7,
        SAN: 4,
    }

    # Direct flights (undirected edges, expand to directed pairs)
    undirected_edges = [
        (ROM, SAN),
        (SEV, ROM),
        (IST, NAP),
        (NAP, SAN),
        (ROM, NAP),
        (ROM, IST),
    ]
    allowed_pairs = set()
    for a, b in undirected_edges:
        allowed_pairs.add((a, b))
        allowed_pairs.add((b, a))
    allowed_pairs = list(allowed_pairs)

    # Create solver
    s = Solver()

    # Variables for 5 blocks (city segments)
    block_count = 5
    block_city = [Int(f"city_{k}") for k in range(block_count)]
    s_vars = [Int(f"s_{k}") for k in range(block_count)]
    e_vars = [Int(f"e_{k}") for k in range(block_count)]

    # Domain constraints
    for k in range(block_count):
        s.add(And(block_city[k] >= 0, block_city[k] < len(cities)))  # city domain
        s.add(And(s_vars[k] >= 1, s_vars[k] <= total_days))
        s.add(And(e_vars[k] >= 1, e_vars[k] <= total_days))

    # All 5 cities must be visited exactly once (permutation)
    s.add(Distinct(block_city))
    s.add(Or([block_city[0] == i for i in range(5)]))  # redundant but explicit domain
    s.add(Or([block_city[1] == i for i in range(5)]))
    s.add(Or([block_city[2] == i for i in range(5)]))
    s.add(Or([block_city[3] == i for i in range(5)]))
    s.add(Or([block_city[4] == i for i in range(5)]))

    # Helper: duration expression based on city
    def dur_expr(city_var):
        return If(city_var == IST, durations[IST],
               If(city_var == ROM, durations[ROM],
               If(city_var == SEV, durations[SEV],
               If(city_var == NAP, durations[NAP],
               If(city_var == SAN, durations[SAN], 0)))))

    # Structure of the chain with 1-day overlaps for flights
    s.add(s_vars[0] == 1)
    for k in range(block_count):
        s.add(e_vars[k] - s_vars[k] + 1 == dur_expr(block_city[k]))
    for k in range(block_count - 1):
        s.add(s_vars[k + 1] == e_vars[k])  # overlap day is flight day
    s.add(e_vars[-1] == total_days)

    # Only direct flights between consecutive cities
    for k in range(block_count - 1):
        s.add(Or([And(block_city[k] == a, block_city[k + 1] == b) for (a, b) in allowed_pairs]))

    # Event constraints:
    # - Istanbul between day 6 and 7 (and total in Istanbul is 2 days) => exactly days 6-7
    # - Santorini between day 13 and 16 (and total in Santorini is 4 days) => exactly days 13-16
    for k in range(block_count):
        s.add(Implies(block_city[k] == IST, And(s_vars[k] == 6, e_vars[k] == 7)))
        s.add(Implies(block_city[k] == SAN, And(s_vars[k] == 13, e_vars[k] == 16)))

    # Solve
    if s.check() != sat:
        return {"error": "No feasible itinerary found with the given constraints."}

    m = s.model()

    # Extract itinerary
    itinerary = []
    for k in range(block_count):
        c_id = m[block_city[k]].as_long()
        s_day = m[s_vars[k]].as_long()
        e_day = m[e_vars[k]].as_long()
        itinerary.append({
            "day_range": f"Day {s_day}-{e_day}",
            "place": cities[c_id]
        })

    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = solve_itinerary()
    print(json.dumps(result))