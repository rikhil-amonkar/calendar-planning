#!/usr/bin/env python3
import json
from z3 import *

def main():
    # There are 6 cities in total.
    # Our mapping is:
    #   0: Tallinn, 1: Bucharest, 2: Seville, 3: Stockholm, 4: Munich, 5: Milan
    cities = ["Tallinn", "Bucharest", "Seville", "Stockholm", "Munich", "Milan"]
    # Fixed durations for each city (in days)
    durations = [2, 4, 5, 5, 5, 2]
    # Allowed direct flights (bidirectional); for a flight leaving from city i,
    # the next city must be one of the following:
    allowed = {
        0: [3, 4],      # Tallinn can fly to Stockholm or Munich (Stockholm–Tallinn, Munich–Tallinn)
        1: [4],         # Bucharest can fly to Munich (Bucharest–Munich)
        2: [4, 5],      # Seville can fly to Munich or Milan (Munich–Seville, Seville–Milan)
        3: [0, 4, 5],   # Stockholm can fly to Tallinn, Munich or Milan (Stockholm–Tallinn, Munich–Stockholm, Milan–Stockholm)
        4: [0, 1, 2, 3, 5],  # Munich can fly to Tallinn, Bucharest, Seville, Stockholm or Milan
        5: [2, 3, 4]    # Milan can fly to Seville, Stockholm or Munich (Seville–Milan, Milan–Stockholm, Munich–Milan)
    }

    N = 6  # number of segments (cities)

    # Create SMT variables.
    # city_vars[i] is the city visited in the i-th segment
    city_vars = [Int(f"city_{i}") for i in range(N)]
    # s_vars[i] and e_vars[i] are the start and end days (inclusive) for that segment.
    s_vars = [Int(f"s_{i}") for i in range(N)]
    e_vars = [Int(f"e_{i}") for i in range(N)]

    solver = Solver()

    # City numbering: each city variable is an integer in 0..5.
    for i in range(N):
        solver.add(city_vars[i] >= 0, city_vars[i] <= 5)
    # All cities must be visited exactly once.
    solver.add(Distinct(city_vars))

    # Domain for days: they must lie between day 1 and day 18.
    for i in range(N):
        solver.add(s_vars[i] >= 1, s_vars[i] <= 18)
        solver.add(e_vars[i] >= 1, e_vars[i] <= 18)

    # Contiguity Constraints:
    # The trip starts on day 1.
    solver.add(s_vars[0] == 1)
    # When flying, the flight day counts for both the city you leave and the one you arrive in.
    # Hence, for consecutive segments, the start day of the next equals the end day of the previous.
    for i in range(N - 1):
        solver.add(s_vars[i + 1] == e_vars[i])
    # The trip ends on day 18.
    solver.add(e_vars[N - 1] == 18)

    # For each segment, set the duration according to the city.
    # If you are in city X, you must spend exactly durations[X] days there.
    def duration_expr(city_var):
        return If(city_var == 0, 2,
               If(city_var == 1, 4,
               If(city_var == 2, 5,
               If(city_var == 3, 5,
               If(city_var == 4, 5,
               2)))))  # if city_var == 5, duration is 2

    for i in range(N):
        solver.add(e_vars[i] == s_vars[i] + duration_expr(city_vars[i]) - 1)

    # Flight connectivity constraints:
    # For consecutive segments, there must be a direct flight between the cities.
    for i in range(N - 1):
        flight_constraints = []
        for c in range(6):
            # If the current city is 'c', then the next city must be in allowed[c].
            flight_constraints.append(
                Implies(city_vars[i] == c, Or([city_vars[i + 1] == dest for dest in allowed[c]]))
            )
        solver.add(And(flight_constraints))

    # Special time-window constraints:
    # 1. Bucharest (city index 1): Visit relatives between day 1 and 4.
    #    Ensure that the Bucharest segment starts on or before day 4.
    for i in range(N):
        solver.add(Implies(city_vars[i] == 1, s_vars[i] <= 4))
    # 2. Seville (city index 2): Meet friends between day 8 and 12.
    #    Ensure that Seville's segment contains a day in [8,12]. Since Seville is 5 days long,
    #    it must start no earlier than day 4 and no later than day 12, and its end day is s + 4.
    for i in range(N):
        solver.add(Implies(city_vars[i] == 2, And(s_vars[i] >= 4, s_vars[i] <= 12, e_vars[i] >= 8)))
    # 3. Munich (city index 4): Attend a wedding between day 4 and 8.
    #    The Munich segment must start no later than day 8.
    for i in range(N):
        solver.add(Implies(city_vars[i] == 4, s_vars[i] <= 8))

    # Solve the constraints.
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for i in range(N):
            city_index = model.evaluate(city_vars[i]).as_long()
            start_day = model.evaluate(s_vars[i]).as_long()
            end_day = model.evaluate(e_vars[i]).as_long()
            itinerary.append({
                "day_range": f"Day {start_day}-{end_day}",
                "place": cities[city_index]
            })
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print(json.dumps({"error": "No solution found"}))

if __name__ == "__main__":
    main()