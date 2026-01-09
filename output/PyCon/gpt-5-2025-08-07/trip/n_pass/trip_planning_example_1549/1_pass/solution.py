import json
from constraint import Problem, AllDifferentConstraint

def main():
    # Trip parameters
    total_days = 28
    cities = [
        "Prague", "Tallinn", "Warsaw", "Porto", "Naples",
        "Milan", "Lisbon", "Santorini", "Riga", "Stockholm"
    ]
    # Required stays (days counted inclusive; overlap on flight day counts for both)
    durations = {
        "Prague": 5,
        "Tallinn": 3,
        "Warsaw": 2,
        "Porto": 3,
        "Naples": 5,
        "Milan": 3,
        "Lisbon": 5,
        "Santorini": 5,
        "Riga": 4,
        "Stockholm": 2
    }

    # Fixed date windows
    fixed_windows = {
        "Riga": (5, 8),        # Attend show days 5-8
        "Tallinn": (18, 20),   # Visit relatives days 18-20
        "Milan": (24, 26)      # Meet friend days 24-26
    }

    # Build directed adjacency set based on provided direct flights
    edges = set()
    def add_undirected(a, b):
        edges.add((a, b))
        edges.add((b, a))
    def add_directed(a, b):
        edges.add((a, b))

    # Given connections
    add_undirected("Riga", "Prague")
    add_undirected("Stockholm", "Milan")
    add_undirected("Riga", "Milan")
    add_undirected("Lisbon", "Stockholm")
    add_directed("Stockholm", "Santorini")
    add_undirected("Naples", "Warsaw")
    add_undirected("Lisbon", "Warsaw")
    add_undirected("Naples", "Milan")
    add_undirected("Lisbon", "Naples")
    add_directed("Riga", "Tallinn")
    add_undirected("Tallinn", "Prague")
    add_undirected("Stockholm", "Warsaw")
    add_undirected("Riga", "Warsaw")
    add_undirected("Lisbon", "Riga")
    add_undirected("Riga", "Stockholm")
    add_undirected("Lisbon", "Porto")
    add_undirected("Lisbon", "Prague")
    add_undirected("Milan", "Porto")
    add_undirected("Prague", "Milan")
    add_undirected("Lisbon", "Milan")
    add_undirected("Warsaw", "Porto")
    add_undirected("Warsaw", "Tallinn")
    add_undirected("Santorini", "Milan")
    add_undirected("Stockholm", "Prague")
    add_undirected("Stockholm", "Tallinn")
    add_undirected("Warsaw", "Milan")
    add_undirected("Santorini", "Naples")
    add_undirected("Warsaw", "Prague")

    # Create CSP
    N = len(cities)
    problem = Problem()

    # Variables for each position: city, start day, end day
    city_vars = []
    start_vars = []
    end_vars = []
    for i in range(1, N + 1):
        cvar = f"CITY_{i}"
        svar = f"S_{i}"
        evar = f"E_{i}"
        city_vars.append(cvar)
        start_vars.append(svar)
        end_vars.append(evar)
        problem.addVariable(cvar, cities)
        problem.addVariable(svar, range(1, total_days + 1))
        problem.addVariable(evar, range(1, total_days + 1))

    # All different cities
    problem.addConstraint(AllDifferentConstraint(), city_vars)

    # Start and end chain constraints
    # First start day
    problem.addConstraint(lambda s: s == 1, (start_vars[0],))
    # Link S_p = E_{p-1} for p>1
    for i in range(1, N):
        problem.addConstraint(lambda s, prev_e: s == prev_e, (start_vars[i], end_vars[i - 1]))
    # End of last equals total_days
    problem.addConstraint(lambda e: e == total_days, (end_vars[-1],))

    # Duration constraints: E_p = S_p + dur(city) - 1
    for i in range(N):
        problem.addConstraint(
            lambda city, s, e, durs=durations: e == s + durs[city] - 1,
            (city_vars[i], start_vars[i], end_vars[i])
        )

    # Flight adjacency constraints between consecutive cities
    for i in range(N - 1):
        problem.addConstraint(
            lambda c1, c2, ed=edges: (c1, c2) in ed,
            (city_vars[i], city_vars[i + 1])
        )

    # Fixed windows for specific cities
    def fixed_window_constraint(city, s, e, fw=fixed_windows):
        if city in fw:
            return s == fw[city][0] and e == fw[city][1]
        return True

    for i in range(N):
        problem.addConstraint(fixed_window_constraint, (city_vars[i], start_vars[i], end_vars[i]))

    # Solve
    solution = problem.getSolution()

    if not solution:
        print(json.dumps({"itinerary": []}))
        return

    # Build itinerary ordered by position (1..N)
    itinerary = []
    for i in range(N):
        c = solution[city_vars[i]]
        s = solution[start_vars[i]]
        e = solution[end_vars[i]]
        itinerary.append({
            "day_range": f"Day {s}-{e}",
            "place": c
        })

    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()