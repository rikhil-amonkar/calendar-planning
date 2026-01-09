import json
from constraint import Problem, AllDifferentConstraint

def main():
    # Input variables (trip constraints)
    total_days = 22
    cities = ["Berlin", "Split", "Bucharest", "Riga", "Lisbon", "Tallinn", "Lyon"]

    # Required stay lengths (in days). Overlap days count for both cities (flight day counts twice).
    lengths = {
        "Berlin": 5,
        "Split": 3,
        "Bucharest": 3,
        "Riga": 5,
        "Lisbon": 3,
        "Tallinn": 4,
        "Lyon": 5,
    }

    # Fixed windows:
    # - Berlin: Days 1-5 (annual show)
    # - Lyon: Days 7-11 (wedding)
    # - Bucharest: Days 13-15 (relatives)
    fixed_starts = {
        "Berlin": 1,
        "Lyon": 7,
        "Bucharest": 13,
    }

    # Direct flights (directed edges). Undirected statements are modeled both ways.
    undirected_pairs = [
        ("Lisbon", "Bucharest"),
        ("Berlin", "Lisbon"),
        ("Bucharest", "Riga"),
        ("Berlin", "Riga"),
        ("Split", "Lyon"),
        ("Lisbon", "Riga"),
        ("Berlin", "Split"),
        ("Lyon", "Lisbon"),
        ("Berlin", "Tallinn"),
        ("Lyon", "Bucharest"),
    ]
    directed_only = [
        ("Riga", "Tallinn"),
    ]
    edges = set()
    for a, b in undirected_pairs:
        edges.add((a, b))
        edges.add((b, a))
    for a, b in directed_only:
        edges.add((a, b))

    # Build CSP
    problem = Problem()

    # Position variables: order in which cities are visited (1..7)
    for c in cities:
        if c == "Berlin":
            problem.addVariable(f"pos_{c}", [1])  # Start trip in Berlin (Day 1)
        else:
            problem.addVariable(f"pos_{c}", list(range(2, len(cities) + 1)))
    problem.addConstraint(AllDifferentConstraint(), [f"pos_{c}" for c in cities])

    # Start day variables for each city
    for c in cities:
        max_start = total_days - lengths[c] + 1
        domain = list(range(1, max_start + 1))
        if c in fixed_starts:
            domain = [fixed_starts[c]]
        problem.addVariable(f"start_{c}", domain)

    # Core chain and connectivity constraint over all positions and starts
    varnames = [f"pos_{c}" for c in cities] + [f"start_{c}" for c in cities]

    def chain_and_connectivity_constraint(*values):
        assignment = {name: val for name, val in zip(varnames, values)}
        pos = {c: assignment[f"pos_{c}"] for c in cities}
        start = {c: assignment[f"start_{c}"] for c in cities}

        # Order cities by position
        ordered = sorted(cities, key=lambda x: pos[x])

        # Must start in Berlin at position 1 and day 1
        if ordered[0] != "Berlin":
            return False
        if start["Berlin"] != 1:
            return False

        # Enforce chaining of days and connectivity along the sequence
        for i in range(1, len(ordered)):
            prev = ordered[i - 1]
            curr = ordered[i]
            # start[curr] = start[prev] + len(prev) - 1 (overlap flight day counts twice)
            if start[curr] != start[prev] + lengths[prev] - 1:
                return False
            # Direct flight must exist from prev to curr
            if (prev, curr) not in edges:
                return False

        # Ensure the final segment ends exactly on total_days
        last = ordered[-1]
        if start[last] + lengths[last] - 1 != total_days:
            return False

        # Fixed windows already ensured by variable domains, but double-check consistency:
        if start.get("Lyon") != 7:
            return False
        if start.get("Bucharest") != 13:
            return False

        return True

    problem.addConstraint(chain_and_connectivity_constraint, varnames)

    solution = problem.getSolution()
    if not solution:
        print(json.dumps({"error": "No feasible itinerary found given the constraints."}))
        return

    # Build itinerary
    order = sorted(cities, key=lambda c: solution[f"pos_{c}"])
    itinerary = []
    for c in order:
        s = solution[f"start_{c}"]
        e = s + lengths[c] - 1
        itinerary.append({
            "day_range": f"Day {s}-{e}",
            "place": c
        })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()