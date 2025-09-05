from z3 import *
import json

def main():
    # Cities and their fixed durations
    # Index mapping: 0: Krakow, 1: Frankfurt, 2: Oslo, 3: Dubrovnik, 4: Naples
    cities = ["Krakow", "Frankfurt", "Oslo", "Dubrovnik", "Naples"]
    durations = [5, 4, 3, 5, 5]  # days spent in each city

    # Allowed direct flight connections (bidirectional)
    allowed_pairs = [
        (0, 1), (1, 0),  # Frankfurt and Krakow
        (0, 2), (2, 0),  # Krakow and Oslo
        (1, 2), (2, 1),  # Frankfurt and Oslo
        (3, 2), (2, 3),  # Dubrovnik and Oslo
        (3, 1), (1, 3),  # Dubrovnik and Frankfurt
        (4, 2), (2, 4),  # Naples and Oslo
        (4, 3), (3, 4),  # Naples and Dubrovnik
        (4, 1), (1, 4)   # Naples and Frankfurt
    ]

    # Create the solver
    solver = Solver()

    n = 5  # number of cities to visit

    # Decision variable: order[i] is the city at itinerary position i (0-indexed).
    order = [Int(f"order_{i}") for i in range(n)]
    for o in order:
        solver.add(o >= 0, o < n)
    solver.add(Distinct(order))

    # S[i]: start day for block i; E[i]: end day for block i.
    S = [Int(f"S_{i}") for i in range(n)]
    E = [Int(f"E_{i}") for i in range(n)]

    # The trip starts on day 1.
    solver.add(S[0] == 1)

    # Helper: given a city variable, return its duration using If-then-else.
    def duration_expr(city_var):
        return If(city_var == 0, durations[0],
               If(city_var == 1, durations[1],
               If(city_var == 2, durations[2],
               If(city_var == 3, durations[3],
               If(city_var == 4, durations[4], 0)))))

    # For each itinerary block, the block covers [S, E] where E = S + (duration - 1)
    for i in range(n):
        solver.add(E[i] == S[i] + duration_expr(order[i]) - 1)

    # Transition rule: when flying from city at position i to i+1, the flight happens on day E[i]
    # and you are present in both cities on that day.
    for i in range(1, n):
        solver.add(S[i] == E[i-1])

    # Total trip length constraint: The last city's end day is day 18.
    solver.add(E[n-1] == 18)

    # Flight connectivity constraints: consecutive cities must have a direct flight.
    for i in range(n - 1):
        conn_constraints = []
        for (a, b) in allowed_pairs:
            conn_constraints.append(And(order[i] == a, order[i+1] == b))
        solver.add(Or(conn_constraints))

    # Oslo relatives constraint:
    # If you visit Oslo (city index 2), then the Oslo block must include a day between 16 and 18.
    # The Oslo block is [S, E] with E = S + 2. The intersection with [16, 18] is non-empty
    # if S + 2 >= 16  (i.e. S >= 14) and S <= 18.
    for i in range(n):
        solver.add(Implies(order[i] == 2, And(S[i] + 2 >= 16, S[i] <= 18)))

    # Dubrovnik friends constraint:
    # If you visit Dubrovnik (city index 3), then the Dubrovnik block [S, E] must include a day between 5 and 9.
    # Since E = S + 4 for Dubrovnik, the condition is S <= 9.
    for i in range(n):
        solver.add(Implies(order[i] == 3, S[i] <= 9))

    # Check for solution and build itinerary if found
    if solver.check() == sat:
        m = solver.model()
        itinerary = []
        for i in range(n):
            start_day = m[S[i]].as_long()
            end_day = m[E[i]].as_long()
            city_index = m[order[i]].as_long()
            itinerary.append({
                "day_range": f"Day {start_day}-{end_day}",
                "place": cities[city_index]
            })
        output = {"itinerary": itinerary}
        print(json.dumps(output))
    else:
        print(json.dumps({"error": "No valid itinerary found"}))

if __name__ == "__main__":
    main()