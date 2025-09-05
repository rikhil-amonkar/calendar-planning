import json
from z3 import *

def main():
    solver = Solver()

    # Map city IDs to names and fixed duration requirements.
    # IDs: 0: Rome, 1: Mykonos, 2: Riga, 3: Munich, 4: Bucharest, 5: Nice, 6: Krakow
    city_names = {
        0: "Rome",
        1: "Mykonos",
        2: "Riga",
        3: "Munich",
        4: "Bucharest",
        5: "Nice",
        6: "Krakow"
    }
    durations = {
        0: 4,  # Rome must be visited 4 days; also conference on day 1 and 4.
        1: 3,  # Mykonos 3 days (wedding must fall between day 4 and 6)
        2: 3,  # Riga 3 days.
        3: 4,  # Munich 4 days.
        4: 4,  # Bucharest 4 days.
        5: 3,  # Nice 3 days.
        6: 2   # Krakow 2 days (annual show from day16 to day17)
    }

    num_segments = 7  # We plan 7 city segments.
    # Decision variables: itinerary order (each segment is a city id) and start day for each segment.
    cities = [Int(f"city_{i}") for i in range(num_segments)]
    starts = [Int(f"start_{i}") for i in range(num_segments)]

    # Fixed segments: The trip must start in Rome and end in Krakow.
    solver.add(cities[0] == 0)      # Rome is city 0.
    solver.add(cities[num_segments - 1] == 6)  # Krakow is city 6.

    # All cities must be visited exactly once.
    solver.add(Distinct(cities))
    for i in range(num_segments):
        solver.add(cities[i] >= 0, cities[i] <= 6)

    # Our trip starts on Day 1.
    solver.add(starts[0] == 1)

    # Define a helper function to get the duration (in days) of a segment 
    # based on the city id.
    def duration_expr(c):
        return If(c == 0, 4,
               If(c == 1, 3,
               If(c == 2, 3,
               If(c == 3, 4,
               If(c == 4, 4,
               If(c == 5, 3, 2))))))
    
    # The itinerary segments are contiguous, but flights cause an overlap.
    # If a flight from city A to city B occurs on day X then day X counts in both segments.
    # Thus, if a segment i (in city X) has duration d, then the next segment starts on:
    # start[i+1] = start[i] + d - 1.
    for i in range(num_segments - 1):
        solver.add(starts[i+1] == starts[i] + duration_expr(cities[i]) - 1)

    # The last segment (Krakow) must start on Day 16.
    # Then its 2-day duration covers Day 16 and Day 17.
    solver.add(starts[num_segments - 1] == 16)
    solver.add(starts[num_segments - 1] + duration_expr(cities[num_segments - 1]) - 1 == 17)

    # Wedding constraint in Mykonos:
    # If a segment is Mykonos (id 1), its interval [start, start+2] must overlap [4,6].
    for i in range(num_segments):
        solver.add(Implies(cities[i] == 1, And(starts[i] <= 6, starts[i] + 3 - 1 >= 4)))

    # Allowed direct flights between cities (with some directional constraints).
    # The flights given (bidirectional unless stated otherwise) are:
    # - Nice ↔ Riga
    # - Bucharest ↔ Munich
    # - Mykonos ↔ Munich
    # - Riga ↔ Bucharest
    # - Rome ↔ Nice
    # - Rome ↔ Munich
    # - Mykonos ↔ Nice
    # - Rome ↔ Mykonos
    # - Munich ↔ Krakow
    # - Rome ↔ Bucharest
    # - Nice ↔ Munich
    # - Riga -> Munich (directional only)
    # - Rome -> Riga (directional only)
    allowed_flights = [
        (0, 1), (1, 0),         # Rome ↔ Mykonos
        (0, 5), (5, 0),         # Rome ↔ Nice
        (0, 3), (3, 0),         # Rome ↔ Munich
        (0, 4), (4, 0),         # Rome ↔ Bucharest
        (0, 2),                # Rome -> Riga (directional)
        (1, 3), (3, 1),         # Mykonos ↔ Munich
        (1, 5), (5, 1),         # Mykonos ↔ Nice
        (2, 5), (5, 2),         # Nice ↔ Riga
        (2, 4), (4, 2),         # Riga ↔ Bucharest
        (2, 3),                # Riga -> Munich (directional)
        (3, 4), (4, 3),         # Bucharest ↔ Munich
        (3, 6), (6, 3),         # Munich ↔ Krakow
        (5, 3), (3, 5)          # Nice ↔ Munich
    ]
    
    def allowed_transition(a, b):
        conds = []
        for (x, y) in allowed_flights:
            conds.append(And(a == x, b == y))
        return Or(conds)
    
    # For every consecutive pair of segments, enforce that a direct flight exists.
    for i in range(num_segments - 1):
        solver.add(allowed_transition(cities[i], cities[i+1]))

    # Solve the constraints.
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for i in range(num_segments):
            city_val = model.evaluate(cities[i]).as_long()
            start_day = model.evaluate(starts[i]).as_long()
            dur = durations[city_val]
            end_day = start_day + dur - 1
            itinerary.append({
                "day_range": f"Day {start_day}-{end_day}",
                "place": city_names[city_val]
            })
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()