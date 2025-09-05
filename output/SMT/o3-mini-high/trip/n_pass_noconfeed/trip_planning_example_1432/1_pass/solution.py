from z3 import *
import json

def main():
    solver = Solver()
    
    # List of 10 cities and their required durations if counted individually.
    # Note: Flight days count for both departure and arrival cities.
    cities = ["Frankfurt", "Salzburg", "Athens", "Reykjavik", "Bucharest", "Valencia", "Vienna", "Amsterdam", "Stockholm", "Riga"]
    # Durations corresponding to each city:
    # Frankfurt:4, Salzburg:5, Athens:5, Reykjavik:5, Bucharest:3, Valencia:2,
    # Vienna:5, Amsterdam:3, Stockholm:3, Riga:3.
    
    # We will decide an ordering (a permutation of indices 0..9) where the itinerary
    # segments are placed consecutively with one overlapping day between segments (flight day).
    # Let order[i] be the city index in position i (0-indexed for itinerary segments).
    order_vars = [Int(f"order_{i}") for i in range(10)]
    # Let S[i] be the start day of the segment in position i. The segment for city X (with duration d)
    # covers days from S[i] to S[i] + d - 1. Note that S[i+1] will equal S[i] + d - 1 (overlapping flight day).
    S = [Int(f"S_{i}") for i in range(10)]
    
    # Define a helper function to return the required duration given a city index.
    def duration_expr(x):
        return If(x == 0, 4,
               If(x == 1, 5,
               If(x == 2, 5,
               If(x == 3, 5,
               If(x == 4, 3,
               If(x == 5, 2,
               If(x == 6, 5,
               If(x == 7, 3,
               If(x == 8, 3,
                  3)))))))))
    
    # Each order variable must be one of the 10 city indices.
    for ov in order_vars:
        solver.add(ov >= 0, ov <= 9)
    # All cities must be visited exactly once.
    solver.add(Distinct(order_vars))
    
    # S variables represent calendar days in [1, 29]
    for s in S:
        solver.add(s >= 1, s <= 29)
    
    # The first segment starts on Day 1.
    solver.add(S[0] == 1)
    
    # For each consecutive segment, enforce the flight rule:
    # If you fly from city A (segment i) to city B (segment i+1) on day X, then the flight day (day X)
    # is counted in both segments.
    # Thus, for segment i, the interval is [S[i], S[i] + duration(A) - 1],
    # and we require that S[i+1] equals the overlapping flight day, i.e.:
    #    S[i+1] = S[i] + duration(order_vars[i]) - 1.
    for i in range(9):
        solver.add(S[i+1] == S[i] + duration_expr(order_vars[i]) - 1)
    
    # Total itinerary days = (sum of individual durations) - (# of flights)
    # With 10 segments, there are 9 flights, so enforce that the end day equals 29.
    solver.add(S[9] + duration_expr(order_vars[9]) - 1 == 29)
    
    # Event constraints:
    # 1. In Athens (city index 2, duration 5): Attend a workshop between Day 14 and 18.
    #    For the segment in Athens, its interval [S, S+4] must intersect [14, 18].
    #    This is ensured by S <= 18 and S + 4 >= 14, i.e. S is between 10 and 18.
    # 2. In Vienna (city index 6, duration 5): Attend a wedding between Day 6 and 10.
    #    Enforce S <= 10 and S + 4 >= 6, i.e. S is between 2 and 10.
    # 3. In Stockholm (city index 8, duration 3): Meet a friend between Day 1 and 3.
    #    Enforce S <= 3. (Since S >= 1 by default.)
    # 4. In Riga (city index 9, duration 3): Attend a conference between Day 18 and 20.
    #    Enforce S <= 20 and S + 2 >= 18, i.e. S is between 16 and 20.
    for i in range(10):
        solver.add(Implies(order_vars[i] == 2, And(S[i] >= 10, S[i] <= 18)))
        solver.add(Implies(order_vars[i] == 6, And(S[i] >= 2, S[i] <= 10)))
        solver.add(Implies(order_vars[i] == 8, S[i] <= 3))
        solver.add(Implies(order_vars[i] == 9, And(S[i] >= 16, S[i] <= 20)))
    
    # Define the allowed direct flights based on the given list.
    # For entries with "and" we assume bidirectional flights.
    # For entries with "from" we assume a one-way flight in that direction only.
    allowed_edges = [
        (5, 0), (0, 5),                           # Valencia <-> Frankfurt
        (6, 4), (4, 6),                           # Vienna <-> Bucharest
        (5, 2),                                  # from Valencia to Athens
        (2, 4), (4, 2),                           # Athens <-> Bucharest
        (9, 0), (0, 9),                           # Riga <-> Frankfurt
        (8, 2), (2, 8),                           # Stockholm <-> Athens
        (7, 4), (4, 7),                           # Amsterdam <-> Bucharest
        (2, 9),                                  # from Athens to Riga
        (7, 0), (0, 7),                           # Amsterdam <-> Frankfurt
        (8, 6), (6, 8),                           # Stockholm <-> Vienna
        (6, 9), (9, 6),                           # Vienna <-> Riga
        (7, 3), (3, 7),                           # Amsterdam <-> Reykjavik
        (3, 0), (0, 3),                           # Reykjavik <-> Frankfurt
        (8, 7), (7, 8),                           # Stockholm <-> Amsterdam
        (7, 5), (5, 7),                           # Amsterdam <-> Valencia
        (6, 0), (0, 6),                           # Vienna <-> Frankfurt
        (5, 4), (4, 5),                           # Valencia <-> Bucharest
        (4, 0), (0, 4),                           # Bucharest <-> Frankfurt
        (8, 0), (0, 8),                           # Stockholm <-> Frankfurt
        (5, 6), (6, 5),                           # Valencia <-> Vienna
        (3, 2),                                  # from Reykjavik to Athens
        (0, 1), (1, 0),                           # Frankfurt <-> Salzburg
        (7, 6), (6, 7),                           # Amsterdam <-> Vienna
        (8, 3), (3, 8),                           # Stockholm <-> Reykjavik
        (7, 9), (9, 7),                           # Amsterdam <-> Riga
        (8, 9), (9, 8),                           # Stockholm <-> Riga
        (6, 3), (3, 6),                           # Vienna <-> Reykjavik
        (7, 2), (2, 7),                           # Amsterdam <-> Athens
        (2, 0), (0, 2),                           # Athens <-> Frankfurt
        (6, 2), (2, 6),                           # Vienna <-> Athens
        (9, 4), (4, 9)                            # Riga <-> Bucharest
    ]
    
    # For each adjacent pair in the itinerary, the flight taken from city A to city B must be a direct flight.
    for i in range(9):
        flight_possible = []
        for (a, b) in allowed_edges:
            flight_possible.append(And(order_vars[i] == a, order_vars[i+1] == b))
        solver.add(Or(flight_possible))
    
    # Check if the constraints can be satisfied.
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for i in range(10):
            city_index = model.evaluate(order_vars[i]).as_long()
            start_day = model.evaluate(S[i]).as_long()
            dur = model.evaluate(duration_expr(order_vars[i])).as_long()
            end_day = start_day + dur - 1
            itinerary.append({
                "day_range": f"Day {start_day}-{end_day}",
                "place": cities[city_index]
            })
        output = {"itinerary": itinerary}
        print(json.dumps(output))
    else:
        print(json.dumps({"error": "No solution found"}))

if __name__ == "__main__":
    main()