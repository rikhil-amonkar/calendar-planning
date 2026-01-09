import json
from constraint import Problem, AllDifferentConstraint

def main():
    # Define cities and constraints
    cities = ["Geneva", "Munich", "Valencia", "Bucharest", "Stuttgart"]
    total_days = 17

    # Durations per city (days in each city, inclusive of flight day overlaps)
    durations = {
        "Stuttgart": 2,
        "Bucharest": 2,
        "Geneva": 4,
        "Valencia": 6,
        "Munich": 7,
    }

    # Direct flight edges (undirected)
    direct_edges = {
        frozenset(("Geneva", "Munich")),
        frozenset(("Munich", "Valencia")),
        frozenset(("Bucharest", "Valencia")),
        frozenset(("Munich", "Bucharest")),
        frozenset(("Valencia", "Stuttgart")),
        frozenset(("Geneva", "Valencia")),
    }

    # Windows
    relatives_geneva_window = (1, 4)  # Visit relatives between day 1 and day 4
    friends_munich_window = (4, 10)   # Meet friends in Munich between day 4 and day 10

    # Set up CSP
    problem = Problem()

    # Variables for the order: city_0 ... city_4 (sequence of visited cities)
    city_vars = [f"city_{i}" for i in range(5)]
    for cv in city_vars:
        problem.addVariable(cv, cities)
    problem.addConstraint(AllDifferentConstraint(), city_vars)

    # Variables for start days of each segment
    start_vars = [f"start_{i}" for i in range(5)]
    for sv in start_vars:
        problem.addVariable(sv, range(1, total_days + 1))

    # First segment must start on day 1
    problem.addConstraint(lambda s: s == 1, ("start_0",))

    # Adjacency must be direct flights
    for i in range(4):
        def adjacency(ca, cb, edges=direct_edges):
            return frozenset((ca, cb)) in edges
        problem.addConstraint(adjacency, (f"city_{i}", f"city_{i+1}"))

    # Link start times with durations: start_{i+1} = start_i + duration(city_i) - 1
    for i in range(4):
        def link_times(s_i, s_next, c_i, durs=durations):
            return s_next == s_i + durs[c_i] - 1
        problem.addConstraint(link_times, (f"start_{i}", f"start_{i+1}", f"city_{i}"))

    # End of last city must be on total_days: start_4 + duration(city_4) - 1 = total_days
    def end_on_total(s4, c4, durs=durations, T=total_days):
        return s4 + durs[c4] - 1 == T
    problem.addConstraint(end_on_total, ("start_4", "city_4"))

    # Geneva relatives window: Geneva's 4 days must be entirely between day 1 and day 4
    # This effectively fixes Geneva to start on day 1 (and end on day 4).
    for i in range(5):
        def geneva_window(c, s, durs=durations, win=relatives_geneva_window):
            if c != "Geneva":
                return True
            # Fully within window
            start_ok = s >= win[0]
            end_ok = s + durs["Geneva"] - 1 <= win[1]
            return start_ok and end_ok
        problem.addConstraint(geneva_window, (f"city_{i}", f"start_{i}"))

    # Munich friends window: 7-day stay must overlap [4,10]
    for i in range(5):
        def munich_overlap(c, s, durs=durations, win=friends_munich_window):
            if c != "Munich":
                return True
            start = s
            end = s + durs["Munich"] - 1
            # Overlap condition with [win[0], win[1]]
            return (start <= win[1]) and (end >= win[0])
        problem.addConstraint(munich_overlap, (f"city_{i}", f"start_{i}"))

    # Solve
    solutions = problem.getSolutions()

    if not solutions:
        print(json.dumps({"error": "No feasible itinerary found given the constraints."}))
        return

    # Choose the first solution (deterministic enough under the constraints)
    sol = solutions[0]

    # Build itinerary segments ordered by position 0..4
    itinerary = []
    for i in range(5):
        city = sol[f"city_{i}"]
        s = sol[f"start_{i}"]
        e = s + durations[city] - 1
        itinerary.append({
            "day_range": f"Day {s}-{e}",
            "place": city
        })

    output = {"itinerary": itinerary}
    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()