from z3 import *
import json

def required_duration(city):
    # Returns the required duration based on the city index.
    # City indices:
    # 0: Stockholm (3 days)
    # 1: Hamburg (5 days)
    # 2: Florence (2 days)
    # 3: Istanbul (5 days)
    # 4: Oslo (5 days)
    # 5: Vilnius (5 days)
    # 6: Santorini (2 days)
    # 7: Munich (5 days)
    # 8: Frankfurt (4 days)
    # 9: Krakow (5 days)
    return If(city == 0, 3,
           If(city == 1, 5,
           If(city == 2, 2,
           If(city == 3, 5,
           If(city == 4, 5,
           If(city == 5, 5,
           If(city == 6, 2,
           If(city == 7, 5,
           If(city == 8, 4, 5)))))))))

def main():
    solver = Solver()

    # List of cities as given
    cities = ["Stockholm", "Hamburg", "Florence", "Istanbul", "Oslo", "Vilnius", "Santorini", "Munich", "Frankfurt", "Krakow"]
    n_cities = len(cities)

    # Decision variables:
    # order[i]: the index of the city visited in the i-th segment (0-indexed)
    # S[i]: the start day for the i-th segment
    # E[i]: the end day for the i-th segment
    # F[i]: a Boolean variable indicating if the flight from segment i to i+1 is on the same day (overlap)
    order = [Int(f"order_{i}") for i in range(n_cities)]
    S = [Int(f"S_{i}") for i in range(n_cities)]
    E = [Int(f"E_{i}") for i in range(n_cities)]
    F = [Bool(f"F_{i}") for i in range(n_cities - 1)]  # transitions from segment i to i+1

    # Domain and distinctness constraints for the itinerary order.
    for i in range(n_cities):
        solver.add(order[i] >= 0, order[i] < n_cities)
    solver.add(Distinct(order))

    # Scheduling constraints: For each segment, assign start and end days.
    for i in range(n_cities):
        solver.add(S[i] >= 1, S[i] <= 32)
        solver.add(E[i] >= 1, E[i] <= 32)
        # The duration of the stay equals the required days for the city.
        solver.add(E[i] == S[i] + required_duration(order[i]) - 1)
    
    # The trip must start on day 1.
    solver.add(S[0] == 1)
    
    # Transition constraints between segments:
    # If you fly on the same day (F[i] is True), then the next segment starts on the same day this segment ends.
    # Otherwise, there is at least a one-day gap (S[i+1] >= E[i] + 1).
    for i in range(n_cities - 1):
        solver.add(Implies(F[i], S[i+1] == E[i]))
        solver.add(Implies(Not(F[i]), S[i+1] >= E[i] + 1))
    
    # The total distinct itinerary days should be 32.
    # When flying on the same day, the flight day is double‐counted in segments. Thus, total days = sum(required_days) - (# same-day flights).
    # Sum of required days = 36, so we need exactly 4 same-day flights:
    solver.add(Sum([If(F[i], 1, 0) for i in range(n_cities - 1)]) == 4)
    
    # The trip must finish on day 32.
    solver.add(E[n_cities - 1] == 32)
    
    # Allowed direct flight connections.
    # Note: Some edges are symmetric and others (marked "from") are only allowed in one direction.
    # Using the following city indices:
    # 0: Stockholm, 1: Hamburg, 2: Florence, 3: Istanbul, 4: Oslo, 5: Vilnius,
    # 6: Santorini, 7: Munich, 8: Frankfurt, 9: Krakow.
    allowed_connections = [
        (4, 0), (0, 4),                    # Oslo <-> Stockholm
        (9, 8), (8, 9),                    # Krakow <-> Frankfurt
        (9, 3), (3, 9),                    # Krakow <-> Istanbul
        (7, 0), (0, 7),                    # Munich <-> Stockholm
        (1, 0), (0, 1),                    # Hamburg <-> Stockholm
        (9, 5),                           # Krakow -> Vilnius
        (4, 3), (3, 4),                    # Oslo <-> Istanbul
        (3, 0), (0, 3),                    # Istanbul <-> Stockholm
        (4, 9), (9, 4),                    # Oslo <-> Krakow
        (5, 3), (3, 5),                    # Vilnius <-> Istanbul
        (4, 5), (5, 4),                    # Oslo <-> Vilnius
        (8, 3), (3, 8),                    # Frankfurt <-> Istanbul
        (4, 8), (8, 4),                    # Oslo <-> Frankfurt
        (7, 1), (1, 7),                    # Munich <-> Hamburg
        (7, 3), (3, 7),                    # Munich <-> Istanbul
        (4, 7), (7, 4),                    # Oslo <-> Munich
        (8, 2), (2, 8),                    # Frankfurt <-> Florence
        (4, 1), (1, 4),                    # Oslo <-> Hamburg
        (5, 8), (8, 5),                    # Vilnius <-> Frankfurt
        (2, 7),                           # Florence -> Munich
        (9, 7), (7, 9),                    # Krakow <-> Munich
        (1, 3), (3, 1),                    # Hamburg <-> Istanbul
        (8, 0), (0, 8),                    # Frankfurt <-> Stockholm
        (0, 6),                           # Stockholm -> Santorini
        (8, 7), (7, 8),                    # Frankfurt <-> Munich
        (6, 4),                           # Santorini -> Oslo
        (9, 0), (0, 9),                    # Krakow <-> Stockholm
        (5, 7),                           # Vilnius -> Munich
        (8, 1), (1, 8)                     # Frankfurt <-> Hamburg
    ]
    
    # Connectivity constraint: the consecutive cities in the itinerary must be connected by a direct flight.
    for i in range(n_cities - 1):
        allowed = []
        for (a, b) in allowed_connections:
            allowed.append(And(order[i] == a, order[i+1] == b))
        solver.add(Or(allowed))
    
    # Special constraints:
    # Workshop in Krakow between day 5 and day 9.
    # If a segment is in Krakow (index 9), then its stay [S, E] must intersect [5, 9].
    for i in range(n_cities):
        solver.add(Implies(order[i] == 9, And(S[i] <= 9, E[i] >= 5)))
    
    # Istanbul annual show: need to be in Istanbul (index 3) during some day in [25, 29].
    for i in range(n_cities):
        solver.add(Implies(order[i] == 3, And(S[i] <= 29, E[i] >= 25)))
    
    if solver.check() == sat:
        m = solver.model()
        itinerary = []
        for i in range(n_cities):
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
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()