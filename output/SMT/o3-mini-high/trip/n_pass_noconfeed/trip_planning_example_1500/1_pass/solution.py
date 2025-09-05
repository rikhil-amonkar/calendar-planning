import json
from z3 import *

def get_duration(city):
    # Map city index to duration using nested Ifs.
    # Cities: 0: London (3), 1: Zurich (2), 2: Bucharest (2), 3: Hamburg (5),
    # 4: Barcelona (4), 5: Reykjavik (5), 6: Stuttgart (5), 7: Stockholm (2),
    # 8: Tallinn (4), 9: Milan (5)
    return If(city == 0, 3,
           If(city == 1, 2,
           If(city == 2, 2,
           If(city == 3, 5,
           If(city == 4, 4,
           If(city == 5, 5,
           If(city == 6, 5,
           If(city == 7, 2,
           If(city == 8, 4,
              5)))))))))

def main():
    # List of cities and their corresponding durations
    cities = ["London", "Zurich", "Bucharest", "Hamburg", "Barcelona",
              "Reykjavik", "Stuttgart", "Stockholm", "Tallinn", "Milan"]
    durations = [3, 2, 2, 5, 4, 5, 5, 2, 4, 5]  # same order as cities

    # Allowed flights as pairs (from, to). 
    # "A and B" flights are bidirectional, except for "from Reykjavik to Stuttgart"
    allowed_flights = [
        (0, 3), (3, 0),                 # London <-> Hamburg
        (0, 5), (5, 0),                 # London <-> Reykjavik
        (9, 4), (4, 9),                 # Milan <-> Barcelona
        (5, 4), (4, 5),                 # Reykjavik <-> Barcelona
        (5, 6),                       # from Reykjavik to Stuttgart (directional)
        (7, 5), (5, 7),                 # Stockholm <-> Reykjavik
        (0, 6), (6, 0),                 # London <-> Stuttgart
        (9, 1), (1, 9),                 # Milan <-> Zurich
        (0, 4), (4, 0),                 # London <-> Barcelona
        (7, 3), (3, 7),                 # Stockholm <-> Hamburg
        (1, 4), (4, 1),                 # Zurich <-> Barcelona
        (7, 6), (6, 7),                 # Stockholm <-> Stuttgart
        (9, 3), (3, 9),                 # Milan <-> Hamburg
        (7, 8), (8, 7),                 # Stockholm <-> Tallinn
        (3, 2), (2, 3),                 # Hamburg <-> Bucharest
        (0, 2), (2, 0),                 # London <-> Bucharest
        (9, 7), (7, 9),                 # Milan <-> Stockholm
        (6, 3), (3, 6),                 # Stuttgart <-> Hamburg
        (0, 1), (1, 0),                 # London <-> Zurich
        (9, 5), (5, 9),                 # Milan <-> Reykjavik
        (0, 7), (7, 0),                 # London <-> Stockholm
        (9, 6), (6, 9),                 # Milan <-> Stuttgart
        (7, 4), (4, 7),                 # Stockholm <-> Barcelona
        (0, 9), (9, 0),                 # London <-> Milan
        (1, 3), (3, 1),                 # Zurich <-> Hamburg
        (2, 4), (4, 2),                 # Bucharest <-> Barcelona
        (1, 7), (7, 1),                 # Zurich <-> Stockholm
        (4, 8), (8, 4),                 # Barcelona <-> Tallinn
        (1, 5), (5, 1),                 # Zurich <-> Reykjavik
        (1, 2), (2, 1)                  # Zurich <-> Bucharest
    ]

    solver = Solver()

    # Create decision variables:
    # perm[i] will be the city index for the i-th segment
    perm = [Int(f"perm_{i}") for i in range(10)]
    # S[i] will be the start day for segment i.
    S_days = [Int(f"S_{i}") for i in range(10)]

    # Constrain permutation to be a permutation over 0..9.
    solver.add(Distinct(perm))
    for i in range(10):
        solver.add(perm[i] >= 0, perm[i] < 10)

    # London (index 0) must be the first stop to attend the annual show from Day 1-3.
    solver.add(perm[0] == 0)
    # The trip starts on Day 1.
    solver.add(S_days[0] == 1)

    # The segments are contiguous with a one-day overlap on flights.
    # For segment i, the finish day = S_days[i] + duration - 1.
    # For i from 0 to 8, the next segment starts on the finish day of segment i.
    for i in range(9):
        solver.add(S_days[i+1] == S_days[i] + (get_duration(perm[i]) - 1))
    
    # The final segment must end on Day 28.
    solver.add(S_days[9] + get_duration(perm[9]) - 1 == 28)

    # Specific city schedule constraints:
    for i in range(10):
        # Zurich (index 1) must be visited for 2 days with the conference on Day 7 and Day 8.
        solver.add(Implies(perm[i] == 1, S_days[i] == 7))
        # Reykjavik (index 5) must be visited for 5 days and must include Day 9 (relatives visit: Days 9-13).
        solver.add(Implies(perm[i] == 5, S_days[i] == 9))
        # Milan (index 9) must be visited for 5 days and friends touring must occur between Day 3 and Day 7.
        solver.add(Implies(perm[i] == 9, S_days[i] <= 7))

    # Constrain flight transitions between consecutive segments.
    for i in range(9):
        flight_options = []
        for (a, b) in allowed_flights:
            flight_options.append(And(perm[i] == a, perm[i+1] == b))
        solver.add(Or(flight_options))

    # Solve the constraints.
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for i in range(10):
            city_index = model.evaluate(perm[i]).as_long()
            start_day = model.evaluate(S_days[i]).as_long()
            # Use the fixed durations list because each city duration is known.
            dur = durations[city_index]
            finish_day = start_day + dur - 1
            itinerary.append({
                "day_range": f"Day {start_day}-{finish_day}",
                "place": cities[city_index]
            })
        output = {"itinerary": itinerary}
        print(json.dumps(output))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()