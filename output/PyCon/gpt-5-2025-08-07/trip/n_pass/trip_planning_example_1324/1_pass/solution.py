import json
from constraint import Problem, AllDifferentConstraint

def main():
    # Define cities and durations
    cities = [
        "Venice", "Barcelona", "Copenhagen", "Lyon",
        "Reykjavik", "Dubrovnik", "Athens", "Tallinn", "Munich"
    ]
    durations = {
        "Venice": 4,
        "Barcelona": 3,
        "Copenhagen": 4,
        "Lyon": 4,
        "Reykjavik": 4,
        "Dubrovnik": 5,
        "Athens": 2,
        "Tallinn": 5,
        "Munich": 3
    }

    # Build directed flight set
    flights = set()
    def add_bidirectional(a, b):
        flights.add((a, b))
        flights.add((b, a))
    def add_direct(a, b):
        flights.add((a, b))

    # Input flight data
    add_bidirectional("Copenhagen", "Athens")
    add_bidirectional("Copenhagen", "Dubrovnik")
    add_bidirectional("Munich", "Tallinn")
    add_bidirectional("Copenhagen", "Munich")
    add_bidirectional("Venice", "Munich")
    add_direct("Reykjavik", "Athens")  # Directed
    add_bidirectional("Athens", "Dubrovnik")
    add_bidirectional("Venice", "Athens")
    add_bidirectional("Lyon", "Barcelona")
    add_bidirectional("Copenhagen", "Reykjavik")
    add_bidirectional("Reykjavik", "Munich")
    add_bidirectional("Athens", "Munich")
    add_bidirectional("Lyon", "Munich")
    add_bidirectional("Barcelona", "Reykjavik")
    add_bidirectional("Venice", "Copenhagen")
    add_bidirectional("Barcelona", "Dubrovnik")
    add_bidirectional("Lyon", "Venice")
    add_bidirectional("Dubrovnik", "Munich")
    add_bidirectional("Barcelona", "Athens")
    add_bidirectional("Copenhagen", "Barcelona")
    add_bidirectional("Venice", "Barcelona")
    add_bidirectional("Barcelona", "Munich")
    add_bidirectional("Barcelona", "Tallinn")
    add_bidirectional("Copenhagen", "Tallinn")

    # Problem setup
    problem = Problem()

    # Position variables for cities and start days
    city_vars = [f"C{i}" for i in range(1, 10)]
    start_vars = [f"S{i}" for i in range(1, 10)]

    # Each position must be one of the cities, all different
    for cv in city_vars:
        problem.addVariable(cv, cities)
    problem.addConstraint(AllDifferentConstraint(), city_vars)

    # Start days domains
    for sv in start_vars:
        problem.addVariable(sv, range(1, 27))

    # Start of first city is Day 1
    problem.addConstraint(lambda s: s == 1, ("S1",))

    # Adjacency time constraints: S_{i+1} = S_i + dur(C_i) - 1
    for i in range(1, 9):
        s_i = f"S{i}"
        c_i = f"C{i}"
        s_next = f"S{i+1}"
        def adj_constraint(s_curr, c_curr, s_nxt, durations=durations):
            return s_nxt == s_curr + durations[c_curr] - 1
        problem.addConstraint(adj_constraint, (s_i, c_i, s_next))

    # Final day must end on Day 26: S9 + dur(C9) - 1 = 26
    def end_day_constraint(s_last, c_last, durations=durations):
        return s_last + durations[c_last] - 1 == 26
    problem.addConstraint(end_day_constraint, ("S9", "C9"))

    # Direct flight constraints between consecutive cities
    for i in range(1, 9):
        c_i = f"C{i}"
        c_next = f"C{i+1}"
        def flight_ok(c_from, c_to, flights=flights):
            return (c_from, c_to) in flights
        problem.addConstraint(flight_ok, (c_i, c_next))

    # Window constraints:
    # - Barcelona between day 10 and 12 inclusive
    # - Copenhagen between day 7 and 10 inclusive
    # - Dubrovnik between day 16 and 20 inclusive
    def window_constraint(city_target, s, c, start_min, end_max, durations=durations):
        if c != city_target:
            return True
        e = s + durations[c] - 1
        return not (e < start_min or s > end_max)

    for i in range(1, 10):
        s_i = f"S{i}"
        c_i = f"C{i}"
        problem.addConstraint(lambda s, c, ct="Barcelona": window_constraint(ct, s, c, 10, 12), (s_i, c_i))
        problem.addConstraint(lambda s, c, ct="Copenhagen": window_constraint(ct, s, c, 7, 10), (s_i, c_i))
        problem.addConstraint(lambda s, c, ct="Dubrovnik": window_constraint(ct, s, c, 16, 20), (s_i, c_i))

    solution = problem.getSolution()
    if not solution:
        print(json.dumps({"error": "No feasible itinerary found"}))
        return

    # Build itinerary ordered by positions
    itinerary = []
    for i in range(1, 10):
        city = solution[f"C{i}"]
        start = solution[f"S{i}"]
        end = start + durations[city] - 1
        itinerary.append({
            "day_range": f"Day {start}-{end}",
            "place": city
        })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()