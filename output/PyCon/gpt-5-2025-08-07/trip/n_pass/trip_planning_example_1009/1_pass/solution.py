import json
from constraint import Problem, AllDifferentConstraint

def main():
    # Trip parameters
    total_days = 23
    cities = ["Riga", "Manchester", "Bucharest", "Florence", "Vienna", "Istanbul", "Reykjavik", "Stuttgart"]
    durations = {
        "Riga": 4,
        "Manchester": 5,
        "Bucharest": 4,
        "Florence": 4,
        "Vienna": 2,
        "Istanbul": 2,
        "Reykjavik": 4,
        "Stuttgart": 5,
    }
    # Special day constraints: inclusive ranges you must be in the city
    special_days = {
        "Istanbul": (12, 13),
        "Bucharest": (16, 19),
    }

    # Build directed edge set for allowed direct flights
    def add_undirected(edges, a, b):
        edges.add((a, b))
        edges.add((b, a))

    allowed_edges = set()
    add_undirected(allowed_edges, "Bucharest", "Vienna")
    add_undirected(allowed_edges, "Reykjavik", "Vienna")
    add_undirected(allowed_edges, "Manchester", "Vienna")
    add_undirected(allowed_edges, "Manchester", "Riga")
    add_undirected(allowed_edges, "Riga", "Vienna")
    add_undirected(allowed_edges, "Istanbul", "Vienna")
    add_undirected(allowed_edges, "Vienna", "Florence")
    add_undirected(allowed_edges, "Stuttgart", "Vienna")
    add_undirected(allowed_edges, "Riga", "Bucharest")
    add_undirected(allowed_edges, "Istanbul", "Riga")
    add_undirected(allowed_edges, "Stuttgart", "Istanbul")
    # Directed flight from Reykjavik to Stuttgart
    allowed_edges.add(("Reykjavik", "Stuttgart"))
    add_undirected(allowed_edges, "Istanbul", "Bucharest")
    add_undirected(allowed_edges, "Manchester", "Istanbul")
    add_undirected(allowed_edges, "Manchester", "Bucharest")
    add_undirected(allowed_edges, "Stuttgart", "Manchester")

    # Set up CSP
    problem = Problem()
    positions = [f"P{i}" for i in range(1, 9)]
    problem.addVariables(positions, cities)
    problem.addConstraint(AllDifferentConstraint(), positions)

    # Direct flight adjacency constraint for consecutive positions
    for i in range(1, 8):
        problem.addConstraint(
            lambda a, b, edges=allowed_edges: (a, b) in edges,
            (f"P{i}", f"P{i+1}")
        )

    # Special day constraints, overall timing alignment
    def timing_constraints(*seq):
        seq = list(seq)  # list of cities in order for P1..P8

        # Compute start and end days for each block with overlap rule:
        # S1=1, S_{k+1} = S_k + d_k - 1; E_k = S_k + d_k - 1
        S = [0] * 8
        E = [0] * 8
        for i in range(8):
            if i == 0:
                S[i] = 1
            else:
                S[i] = S[i - 1] + durations[seq[i - 1]] - 1
            E[i] = S[i] + durations[seq[i]] - 1

        # Enforce special city day coverage
        for city, (a, b) in special_days.items():
            if city not in seq:
                return False
            pos = seq.index(city)
            # City coverage must include the special day interval
            if not (S[pos] <= a and E[pos] >= b):
                return False

        # Ensure the final day matches the total days
        if E[-1] != total_days:
            return False

        return True

    problem.addConstraint(timing_constraints, positions)

    solution = problem.getSolution()

    if not solution:
        output = {"itinerary": []}
        print(json.dumps(output, ensure_ascii=False))
        return

    # Build ordered sequence of cities
    ordered = [solution[p] for p in positions]

    # Compute day ranges
    start_days = []
    end_days = []
    for i in range(8):
        if i == 0:
            s = 1
        else:
            s = start_days[i - 1] + durations[ordered[i - 1]] - 1
        e = s + durations[ordered[i]] - 1
        start_days.append(s)
        end_days.append(e)

    itinerary = []
    for i, city in enumerate(ordered):
        itinerary.append({
            "day_range": f"Day {start_days[i]}-{end_days[i]}",
            "place": city
        })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()