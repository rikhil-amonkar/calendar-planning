import json
from z3 import *

def main():
    # City codes and corresponding planned durations:
    # 0: Paris (5 days)
    # 1: Florence (3 days)
    # 2: Vienna (2 days)
    # 3: Porto (3 days)
    # 4: Munich (5 days)
    # 5: Nice (5 days)
    # 6: Warsaw (3 days)
    city_names = {
        0: "Paris",
        1: "Florence",
        2: "Vienna",
        3: "Porto",
        4: "Munich",
        5: "Nice",
        6: "Warsaw"
    }
    durations = {
        0: 5,
        1: 3,
        2: 2,
        3: 3,
        4: 5,
        5: 5,
        6: 3
    }
    
    # Allowed direct flights between cities (using city codes)
    # Note: Most connections are bidirectional except for the special case
    # "from Florence to Munich" which is only allowed in that direction.
    allowed_flights = [
        (1, 2), (2, 1),     # Florence <-> Vienna
        (0, 6), (6, 0),     # Paris <-> Warsaw
        (4, 2), (2, 4),     # Munich <-> Vienna
        (3, 2), (2, 3),     # Porto <-> Vienna
        (6, 2), (2, 6),     # Warsaw <-> Vienna
        (1, 4),            # from Florence to Munich only
        (4, 6), (6, 4),     # Munich <-> Warsaw
        (4, 5), (5, 4),     # Munich <-> Nice
        (0, 1), (1, 0),     # Paris <-> Florence
        (6, 5), (5, 6),     # Warsaw <-> Nice
        (3, 4), (4, 3),     # Porto <-> Munich
        (3, 5), (5, 3),     # Porto <-> Nice
        (0, 2), (2, 0),     # Paris <-> Vienna
        (5, 2), (2, 5),     # Nice <-> Vienna
        (3, 0), (0, 3),     # Porto <-> Paris
        (0, 5), (5, 0),     # Paris <-> Nice
        (0, 4), (4, 0),     # Paris <-> Munich
        (3, 6), (6, 3)      # Porto <-> Warsaw
    ]
    
    solver = Solver()

    # Define the itinerary order:
    # order[i] is an integer representing the city code for the i-th segment (0 <= i <= 6)
    order = [Int(f"order_{i}") for i in range(7)]
    for o in order:
        solver.add(o >= 0, o <= 6)
    solver.add(Distinct(order))  # all cities must be visited exactly once

    # Define the start day S[i] for each segment i.
    # We set the trip to start on day 1.
    S = [Int(f"S_{i}") for i in range(7)]
    solver.add(S[0] == 1)

    # Helper function to return the planned duration for a given city (as a Z3 expression).
    def dur(city):
        return If(city == 0, durations[0],
               If(city == 1, durations[1],
               If(city == 2, durations[2],
               If(city == 3, durations[3],
               If(city == 4, durations[4],
               If(city == 5, durations[5],
               If(city == 6, durations[6],
                  0)))))))

    # The flight mechanism: when flying from segment i to segment i+1,
    # the flight happens on the departure day which is the start day of segment i+1.
    # Thus, we require:
    #   S[0] = 1
    #   S[i+1] = S[i] + dur(order[i]) - 1   for i=0,...,5.
    for i in range(6):
        solver.add(S[i+1] == S[i] + dur(order[i]) - 1)
    
    # The itinerary must end on Day 20.
    # The end day of segment i is defined as: E[i] = S[i] + dur(order[i]) - 1.
    solver.add(S[6] + dur(order[6]) - 1 == 20)
    
    # Flight connectivity constraints: Only allowed direct flights may be taken.
    for i in range(6):
        allowed_transitions = []
        for (a, b) in allowed_flights:
            allowed_transitions.append(And(order[i] == a, order[i+1] == b))
        solver.add(Or(allowed_transitions))
    
    # Time-window constraints for special events.
    # 1. Attend a workshop in Porto (city code 3) between Day 1 and 3.
    #    That requires that Porto's segment starts on Day <= 3.
    for i in range(7):
        solver.add(Implies(order[i] == 3, S[i] <= 3))
    
    # 2. Attend a wedding in Warsaw (city code 6) between Day 13 and 15.
    #    Warsaw's 3-day stay must include at least one day in that window:
    #    This is enforced by requiring S[i] <= 15 and S[i] + 2 >= 13.
    #    Equivalently, S[i] must be in the range [11, 15].
    for i in range(7):
        solver.add(Implies(order[i] == 6, And(S[i] >= 11, S[i] <= 15)))
    
    # 3. Visit relatives in Vienna (city code 2) between Day 19 and 20.
    #    Vienna's 2-day stay must include at least one day in that window:
    #    This is enforced by requiring S[i] <= 19 and S[i] + 1 >= 19,
    #    i.e. S[i] must be in [18, 19].
    for i in range(7):
        solver.add(Implies(order[i] == 2, And(S[i] >= 18, S[i] <= 19)))
    
    # Check for a valid itinerary.
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for i in range(7):
            city_code = model.evaluate(order[i]).as_long()
            start_day = model.evaluate(S[i]).as_long()
            city_duration = durations[city_code]
            end_day = start_day + city_duration - 1
            itinerary.append({
                "day_range": f"Day {start_day}-{end_day}",
                "place": city_names[city_code]
            })
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        # If no itinerary can be found, output an empty itinerary.
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()