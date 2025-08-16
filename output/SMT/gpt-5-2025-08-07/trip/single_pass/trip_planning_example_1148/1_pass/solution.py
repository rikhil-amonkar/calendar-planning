import json
from z3 import *

def solve_itinerary():
    # City indices
    LIS, DBV, CPH, PRG, TLL, STO, SPL, LYO = range(8)
    cities = ["Lisbon", "Dubrovnik", "Copenhagen", "Prague", "Tallinn", "Stockholm", "Split", "Lyon"]
    n_days = 19

    # Direct flights (undirected)
    direct_pairs = [
        ("Dubrovnik", "Stockholm"),
        ("Lisbon", "Copenhagen"),
        ("Lisbon", "Lyon"),
        ("Copenhagen", "Stockholm"),
        ("Copenhagen", "Split"),
        ("Prague", "Stockholm"),
        ("Tallinn", "Stockholm"),
        ("Prague", "Lyon"),
        ("Lisbon", "Stockholm"),
        ("Prague", "Lisbon"),
        ("Stockholm", "Split"),
        ("Prague", "Copenhagen"),
        ("Split", "Lyon"),
        ("Copenhagen", "Dubrovnik"),
        ("Prague", "Split"),
        ("Tallinn", "Copenhagen"),
        ("Tallinn", "Prague"),
    ]
    name_to_idx = {name: i for i, name in enumerate(cities)}
    undirected = set()
    for a, b in direct_pairs:
        i, j = name_to_idx[a], name_to_idx[b]
        undirected.add((i, j))
        undirected.add((j, i))

    # Required total days per city
    total_days = {
        LIS: 2,  # Lisbon
        DBV: 5,  # Dubrovnik
        CPH: 5,  # Copenhagen
        PRG: 3,  # Prague
        TLL: 2,  # Tallinn
        STO: 4,  # Stockholm
        SPL: 3,  # Split
        LYO: 2,  # Lyon
    }

    # We model the trip as a sequence of contiguous city blocks that cover all 19 days.
    # Due to the "flight day counts for both cities" rule, for every city except the last,
    # its contiguous block length must be (total_days[city] - 1). The final city's block
    # has length equal to total_days[city]. We choose Lyon as the final city (fits days 18-19).
    block_len = {
        LIS: total_days[LIS] - 1,  # 1
        DBV: total_days[DBV] - 1,  # 4
        CPH: total_days[CPH] - 1,  # 4
        PRG: total_days[PRG] - 1,  # 2
        TLL: total_days[TLL] - 1,  # 1
        STO: total_days[STO] - 1,  # 3
        SPL: total_days[SPL] - 1,  # 2
        LYO: total_days[LYO],      # 2 (final city)
    }

    s = Solver()

    # Day variables: city at day d (1..19)
    c = [None] + [Int(f"day_{d}") for d in range(1, n_days + 1)]
    for d in range(1, n_days + 1):
        s.add(And(c[d] >= 0, c[d] <= 7))

    # Block start variables for each city
    starts = {i: Int(f"start_{cities[i]}") for i in range(8)}
    for i in range(8):
        # Domain for starts: 1..(19 - block_len[i] + 1)
        s.add(starts[i] >= 1, starts[i] <= n_days - block_len[i] + 1)

    # Fix Lyon as the final block occupying days 18-19
    s.add(starts[LYO] == 18)

    # Link day assignments to city blocks: c[d] == i iff d in [start_i, start_i + len_i - 1]
    for i in range(8):
        length = block_len[i]
        for d in range(1, n_days + 1):
            in_interval = And(d >= starts[i], d <= starts[i] + length - 1)
            s.add((c[d] == i) == in_interval)

    # Adjacency constraints: when changing cities between consecutive days, it must be a direct flight
    for d in range(2, n_days + 1):
        # Either staying same city or taking a direct flight among allowed pairs
        transitions = [And(c[d - 1] == i, c[d] == j) for (i, j) in undirected]
        s.add(Or(c[d] == c[d - 1], Or(transitions)))

    # Presence predicate: a city is "present" on day d if either c[d] is that city,
    # or if there is a flight on day d from that city (i.e., previous day city is it and c[d] != c[d-1]).
    def present(city_idx, d):
        if d == 1:
            return c[1] == city_idx
        return Or(c[d] == city_idx, And(c[d - 1] == city_idx, c[d] != c[d - 1]))

    # Window constraints (at least one day present within the given ranges)
    # Tallinn friend: days 1-2
    s.add(Sum([If(present(TLL, d), 1, 0) for d in [1, 2]]) >= 1)
    # Lisbon workshop: days 4-5
    s.add(Sum([If(present(LIS, d), 1, 0) for d in [4, 5]]) >= 1)
    # Stockholm wedding: days 13-16
    s.add(Sum([If(present(STO, d), 1, 0) for d in range(13, 17)]) >= 1)
    # Lyon show: days 18-19
    s.add(Sum([If(present(LYO, d), 1, 0) for d in [18, 19]]) >= 1)

    # Optional: verify exact city-day totals using presence counting rule
    # (This is redundant given the block construction but keeps the model robust)
    for i in range(8):
        count = Sum([If(c[d] == i, 1, 0) for d in range(1, n_days + 1)]) + \
                Sum([If(And(c[d - 1] == i, c[d] != c[d - 1]), 1, 0) for d in range(2, n_days + 1)])
        s.add(count == total_days[i])

    if s.check() != sat:
        raise RuntimeError("No solution found")

    m = s.model()
    itinerary = []
    for d in range(1, n_days + 1):
        city_idx = m[c[d]].as_long()
        itinerary.append({"day": d, "place": cities[city_idx]})

    print(json.dumps({"itinerary": itinerary}, indent=2))

if __name__ == "__main__":
    solve_itinerary()