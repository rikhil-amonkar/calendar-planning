import json
from constraint import Problem

def build_direct_flights():
    # Cities
    cities = [
        "Geneva", "Madrid", "Venice", "Munich", "Reykjavik",
        "Vienna", "Riga", "Vilnius", "Istanbul", "Brussels"
    ]

    # Initialize directed edges set
    edges = set()

    # Helper to add undirected and directed flights
    def undirected(a, b):
        edges.add((a, b))
        edges.add((b, a))

    def directed(a, b):
        edges.add((a, b))

    # Add flights as per given list
    undirected("Munich", "Vienna")
    undirected("Istanbul", "Brussels")
    undirected("Vienna", "Vilnius")
    undirected("Madrid", "Munich")
    undirected("Venice", "Brussels")
    undirected("Riga", "Brussels")
    undirected("Geneva", "Istanbul")
    undirected("Munich", "Reykjavik")
    undirected("Vienna", "Istanbul")
    undirected("Riga", "Istanbul")
    undirected("Reykjavik", "Vienna")
    undirected("Venice", "Munich")
    undirected("Madrid", "Venice")
    undirected("Vilnius", "Istanbul")
    undirected("Venice", "Vienna")
    undirected("Venice", "Istanbul")
    directed("Reykjavik", "Madrid")
    directed("Riga", "Munich")
    undirected("Munich", "Istanbul")
    undirected("Reykjavik", "Brussels")
    undirected("Vilnius", "Brussels")
    directed("Vilnius", "Munich")
    undirected("Madrid", "Vienna")
    undirected("Vienna", "Riga")
    undirected("Geneva", "Vienna")
    undirected("Madrid", "Brussels")
    undirected("Vienna", "Brussels")
    undirected("Geneva", "Brussels")
    undirected("Geneva", "Madrid")
    undirected("Munich", "Brussels")
    undirected("Madrid", "Istanbul")
    undirected("Geneva", "Munich")
    directed("Riga", "Vilnius")

    return cities, edges

def main():
    # Cities and durations
    durations = {
        "Istanbul": 4,
        "Vienna": 4,
        "Riga": 2,
        "Brussels": 2,
        "Madrid": 4,
        "Vilnius": 4,
        "Venice": 5,
        "Geneva": 4,
        "Munich": 5,
        "Reykjavik": 2
    }

    # Fixed day windows per problem
    fixed_starts = {
        "Geneva": 1,     # Days 1-4
        "Venice": 7,     # Days 7-11
        "Vilnius": 20,   # Days 20-23
        "Brussels": 26   # Days 26-27
    }

    cities, edges = build_direct_flights()

    problem = Problem()

    # Variables for city at each position and start day at each position
    pos_vars = []
    day_vars = []
    for i in range(1, 11):
        ci = f"City_{i}"
        si = f"Start_{i}"
        pos_vars.append(ci)
        day_vars.append(si)
        problem.addVariable(ci, cities)
        problem.addVariable(si, range(1, 28))  # Days 1..27

    # All cities must be used exactly once (pairwise different across positions)
    for i in range(10):
        for j in range(i + 1, 10):
            problem.addConstraint(lambda a, b: a != b, (pos_vars[i], pos_vars[j]))

    # Force first and last city positions based on day constraints
    problem.addConstraint(lambda c: c == "Geneva", (pos_vars[0],))
    problem.addConstraint(lambda s: s == fixed_starts["Geneva"], (day_vars[0],))
    problem.addConstraint(lambda c: c == "Brussels", (pos_vars[9],))
    problem.addConstraint(lambda s: s == fixed_starts["Brussels"], (day_vars[9],))

    # Apply fixed starts for any position where those cities appear
    def fixed_start_constraint(city, start):
        if city in fixed_starts:
            return start == fixed_starts[city]
        return True

    for i in range(10):
        problem.addConstraint(fixed_start_constraint, (pos_vars[i], day_vars[i]))

    # Adjacency constraints: direct flight and overlapping day logic
    def adjacency_constraint(c1, s1, c2, s2):
        # Must have direct flight from c1 to c2
        if (c1, c2) not in edges:
            return False
        # Enforce overlap day: next start = current start + duration(current) - 1
        return s2 == s1 + durations[c1] - 1

    for i in range(9):
        problem.addConstraint(adjacency_constraint, (pos_vars[i], day_vars[i], pos_vars[i+1], day_vars[i+1]))

    # The last city's end day must be day 27 (trip length)
    def last_end_is_27(city, start):
        return start + durations[city] - 1 == 27

    problem.addConstraint(last_end_is_27, (pos_vars[9], day_vars[9]))

    # Solve
    solution = problem.getSolution()
    if not solution:
        print(json.dumps({"error": "No feasible itinerary found with given constraints."}))
        return

    # Build ordered itinerary
    itinerary = []
    for i in range(1, 11):
        city = solution[f"City_{i}"]
        start = solution[f"Start_{i}"]
        end = start + durations[city] - 1
        itinerary.append({
            "day_range": f"Day {start}-{end}",
            "place": city
        })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()