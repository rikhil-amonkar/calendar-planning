import itertools
import json

def find_itinerary():
    # Input variables (constraints)
    total_days = 12
    cities = ["Split", "Helsinki", "Reykjavik", "Vilnius", "Geneva"]
    required_durations = {
        "Split": 2,
        "Helsinki": 2,
        "Reykjavik": 3,
        "Vilnius": 3,
        "Geneva": 6,
    }
    # Windows (inclusive day indices)
    vilnius_window = (7, 9)   # Must be in Vilnius between Day 7 and Day 9 (inclusive)
    reykjavik_window = (10, 12)  # Wedding between Day 10 and Day 12; be in Reykjavik then
    
    # Direct flight connections (undirected)
    edges = {
        frozenset(["Split", "Helsinki"]),
        frozenset(["Geneva", "Split"]),
        frozenset(["Geneva", "Helsinki"]),
        frozenset(["Helsinki", "Reykjavik"]),
        frozenset(["Vilnius", "Helsinki"]),
        frozenset(["Split", "Vilnius"]),
    }
    
    # Basic feasibility check: total requested days must equal total_days + (number of flights)
    # With 5 cities visited linearly, number of flights is 4.
    if sum(required_durations.values()) != total_days + (len(cities) - 1):
        raise ValueError("Infeasible duration totals for given trip length and transitions.")
    
    def is_direct(a, b):
        return frozenset([a, b]) in edges
    
    def valid_path(order):
        return all(is_direct(order[i], order[i+1]) for i in range(len(order)-1))
    
    # Given an order, compute inclusive intervals [L_i, R_i] for each city i
    # Interval lengths equal the required durations by construction.
    def compute_intervals(order):
        durations_seq = [required_durations[c] for c in order]
        intervals = []
        # Cumulative sums
        S = []
        s = 0
        for d in durations_seq:
            s += d
            S.append(s)
        # Intervals:
        # city 0: [1, S0-0]
        # city i: [S_{i-1}-(i-1), S_i - i] for i >= 1
        for i, city in enumerate(order):
            if i == 0:
                L = 1
                R = S[0] - 0
            else:
                L = S[i-1] - (i-1)
                R = S[i] - i
            intervals.append((city, L, R))
        return intervals
    
    def interval_includes(interval, window):
        L, R = interval
        a, b = window
        return L <= a and R >= b
    
    # Search for a feasible Hamiltonian path (order) and corresponding flight days/intervals
    best_solution = None
    for order in itertools.permutations(cities):
        if not valid_path(order):
            continue
        intervals = compute_intervals(order)
        # Quick overall sanity: final interval must end at Day 12
        if intervals[-1][2] != total_days:
            continue
        # Check window constraints
        vno_interval = next((L_R for (city, *L_R) in intervals if city == "Vilnius"), None)
        rek_interval = next((L_R for (city, *L_R) in intervals if city == "Reykjavik"), None)
        if vno_interval is None or rek_interval is None:
            continue
        vno_L, vno_R = vno_interval
        rek_L, rek_R = rek_interval
        if not interval_includes((vno_L, vno_R), vilnius_window):
            continue
        if not interval_includes((rek_L, rek_R), reykjavik_window):
            continue
        # Verify each city's interval length matches required duration
        ok = True
        for city, L, R in intervals:
            if (R - L + 1) != required_durations[city]:
                ok = False
                break
        if not ok:
            continue
        best_solution = intervals
        break
    
    if best_solution is None:
        raise RuntimeError("No feasible itinerary found under given constraints.")
    
    # Build output itinerary in requested format
    itinerary = []
    for city, L, R in best_solution:
        day_range = f"Day {L}-{R}"
        itinerary.append({"day_range": day_range, "place": city})
    
    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = find_itinerary()
    print(json.dumps(result, ensure_ascii=False))