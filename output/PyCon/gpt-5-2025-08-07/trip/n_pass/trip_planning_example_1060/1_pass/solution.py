import json
from constraint import Problem, AllDifferentConstraint

def main():
    # Define cities and required stay lengths
    cities = [
        "Stuttgart",
        "Istanbul",
        "Vilnius",
        "Seville",
        "Geneva",
        "Valencia",
        "Munich",
        "Reykjavik",
    ]
    lengths = {
        "Stuttgart": 4,
        "Istanbul": 4,
        "Vilnius": 4,
        "Seville": 3,
        "Geneva": 5,
        "Valencia": 5,
        "Munich": 3,
        "Reykjavik": 4,
    }

    # Directed flight edges (include both directions where specified as "and")
    edges = set()
    def add_undirected(a, b):
        edges.add((a, b))
        edges.add((b, a))
    def add_direct(a, b):
        edges.add((a, b))

    add_undirected("Geneva", "Istanbul")
    add_undirected("Reykjavik", "Munich")
    add_undirected("Stuttgart", "Valencia")
    add_direct("Reykjavik", "Stuttgart")
    add_undirected("Stuttgart", "Istanbul")
    add_undirected("Munich", "Geneva")
    add_undirected("Istanbul", "Vilnius")
    add_undirected("Valencia", "Seville")
    add_undirected("Valencia", "Istanbul")
    add_direct("Vilnius", "Munich")
    add_undirected("Seville", "Munich")
    add_undirected("Munich", "Istanbul")
    add_undirected("Valencia", "Geneva")
    add_undirected("Valencia", "Munich")

    total_days = 25
    total_city_days = sum(lengths[c] for c in cities)
    # number of transitions = number of city changes = 7 for 8 cities
    # sum(city-days) = total_days + transitions -> 32 = 25 + 7 (consistent)

    # Create CSP
    problem = Problem()

    slots = [f"slot{i}" for i in range(1, 9)]
    for s in slots:
        problem.addVariable(s, cities)

    # All cities must be used exactly once
    problem.addConstraint(AllDifferentConstraint(), slots)

    # Reykjavik must be first (workshop Days 1-4)
    problem.addConstraint(lambda s1: s1 == "Reykjavik", ("slot1",))

    # Adjacency and day-anchor constraints
    def adjacency_and_day_constraints(*slot_vals):
        # Check direct flight adjacency (respect direction)
        for i in range(7):
            a = slot_vals[i]
            b = slot_vals[i + 1]
            if (a, b) not in edges:
                return False

        # Compute start days per position: S_k = 1 + sum_{i<k}(L(slot_i)-1)
        starts = [0] * 8
        for k in range(8):
            if k == 0:
                starts[k] = 1
            else:
                starts[k] = starts[k - 1] + (lengths[slot_vals[k - 1]] - 1)

        # Map city -> start day
        S_map = {slot_vals[k]: starts[k] for k in range(8)}
        # End days
        E_map = {c: S_map[c] + lengths[c] - 1 for c in cities}

        # Anchored constraints:
        # Reykjavik Days 1-4 (workshop) -> start at 1 with length 4
        if S_map.get("Reykjavik") != 1:
            return False
        # Stuttgart 4 days and must include Days 4 and 7 -> start 4, end 7
        if S_map.get("Stuttgart") != 4:
            return False
        # Munich must be Days 13-15 (annual show)
        if S_map.get("Munich") != 13:
            return False
        # Istanbul must be Days 19-22 (relatives)
        if S_map.get("Istanbul") != 19:
            return False

        # Ensure last city ends on Day 25
        last_end = starts[7] + lengths[slot_vals[7]] - 1
        if last_end != total_days:
            return False

        # Ensure total structure matches sum(city-days) = total_days + transitions
        # This is implicitly satisfied by construction, but keep a safeguard:
        if total_city_days != total_days + 7:
            return False

        return True

    problem.addConstraint(adjacency_and_day_constraints, tuple(slots))

    solutions = problem.getSolutions()

    if not solutions:
        # If no solution found, output empty itinerary gracefully
        print(json.dumps({"itinerary": []}))
        return

    # Choose the first solution
    sol = solutions[0]
    ordered_cities = [sol[s] for s in slots]

    # Compute starts and ends for the solution
    starts = []
    for i, city in enumerate(ordered_cities):
        if i == 0:
            starts.append(1)
        else:
            prev_city = ordered_cities[i - 1]
            starts.append(starts[-1] + lengths[prev_city] - 1)
    ends = [starts[i] + lengths[ordered_cities[i]] - 1 for i in range(8)]

    itinerary = []
    for i, city in enumerate(ordered_cities):
        itinerary.append({
            "day_range": f"Day {starts[i]}-{ends[i]}",
            "place": city
        })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()