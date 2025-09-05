from z3 import *
import json

def main():
    # Define cities, durations, and direct flight connections (using indices)
    cities = ["Manchester", "Istanbul", "Venice", "Krakow", "Lyon"]
    durations = {
        "Manchester": 3,
        "Istanbul": 7,
        "Venice": 7,
        "Krakow": 6,
        "Lyon": 2
    }
    # Mapping: 0: Manchester, 1: Istanbul, 2: Venice, 3: Krakow, 4: Lyon
    # Allowed direct flights (bidirectional):
    # Manchester-Venice, Manchester-Istanbul, Venice-Istanbul, Istanbul-Krakow,
    # Venice-Lyon, Lyon-Istanbul, Manchester-Krakow.
    allowed_flights = {
        (0, 2), (2, 0),
        (0, 1), (1, 0),
        (2, 1), (1, 2),
        (1, 3), (3, 1),
        (2, 4), (4, 2),
        (4, 1), (1, 4),
        (0, 3), (3, 0)
    }

    solver = Solver()

    num_cities = 5  # itinerary will have 5 segments corresponding to the 5 cities

    # Decision variables:
    # X[i] will hold the city (as an integer code) at itinerary position i (0-indexed).
    X = [Int(f"X{i}") for i in range(num_cities)]
    # S[i] will hold the starting day for the city at position i.
    S = [Int(f"S{i}") for i in range(num_cities)]

    # Domain constraints:
    for i in range(num_cities):
        solver.add(And(X[i] >= 0, X[i] < num_cities))
        solver.add(And(S[i] >= 1, S[i] <= 21))
    solver.add(Distinct(X))  # each city is visited exactly once

    # The itinerary is chained via flight days.
    # For a segment at position i, its end day = S[i] + (duration of X[i]) - 1.
    # If you fly from city A to city B on the same day, then S[i+1] = end(A).
    def duration_expr(x):
        return If(x == 0, durations["Manchester"],
                  If(x == 1, durations["Istanbul"],
                     If(x == 2, durations["Venice"],
                        If(x == 3, durations["Krakow"],
                           durations["Lyon"]))))

    # Set the start of the first city as Day 1.
    solver.add(S[0] == 1)

    # Link the segments: if city at position i has duration d then next city's start equals current end.
    for i in range(num_cities - 1):
        solver.add(S[i + 1] == S[i] + duration_expr(X[i]) - 1)

    # The overall trip must span 21 days.
    # End day of the last city must be 21.
    solver.add(S[num_cities - 1] + duration_expr(X[num_cities - 1]) - 1 == 21)

    # Flight connectivity constraints:
    # For each consecutive pair in the itinerary, there must be a direct flight.
    for i in range(num_cities - 1):
        flight_allowed = []
        for (a, b) in allowed_flights:
            flight_allowed.append(And(X[i] == a, X[i + 1] == b))
        solver.add(Or(flight_allowed))

    # Special event constraints:
    # Wedding in Manchester must be attended between Day 1 and Day 3.
    # If Manchester (code 0) is visited at any position, its start day must be <= 3.
    for i in range(num_cities):
        solver.add(Implies(X[i] == 0, S[i] <= 3))
    
    # Workshop in Venice must be attended between Day 3 and Day 9.
    # If Venice (code 2) is visited, its start day must be <= 9.
    for i in range(num_cities):
        solver.add(Implies(X[i] == 2, S[i] <= 9))

    # Solve the SMT constraints.
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for i in range(num_cities):
            city_index = model.evaluate(X[i]).as_long()
            city_name = cities[city_index]
            start_day = model.evaluate(S[i]).as_long()
            d = durations[city_name]
            end_day = start_day + d - 1
            itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": city_name})
        output = {"itinerary": itinerary}
        print(json.dumps(output))
    else:
        print(json.dumps({"error": "No solution found"}))

if __name__ == '__main__':
    main()