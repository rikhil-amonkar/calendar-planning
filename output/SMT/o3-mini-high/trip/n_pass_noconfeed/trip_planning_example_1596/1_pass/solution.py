from z3 import *
import json

# Define the list of cities and their fixed durations
cities = {
    0: "Bucharest",
    1: "Krakow",
    2: "Munich",
    3: "Barcelona",
    4: "Warsaw",
    5: "Budapest",
    6: "Stockholm",
    7: "Riga",
    8: "Edinburgh",
    9: "Vienna"
}

durations = {
    0: 2,
    1: 4,
    2: 3,
    3: 5,
    4: 5,
    5: 5,
    6: 2,
    7: 5,
    8: 5,
    9: 5
}

# Allowed direct flight connections (bidirectional)
allowed_flights = [
    (5, 2),   # Budapest - Munich
    (0, 7),   # Bucharest - Riga
    (2, 1),   # Munich - Krakow
    (2, 4),   # Munich - Warsaw
    (2, 0),   # Munich - Bucharest
    (8, 6),   # Edinburgh - Stockholm
    (3, 4),   # Barcelona - Warsaw
    (8, 1),   # Edinburgh - Krakow
    (3, 2),   # Barcelona - Munich
    (6, 1),   # Stockholm - Krakow
    (5, 9),   # Budapest - Vienna
    (3, 6),   # Barcelona - Stockholm
    (6, 2),   # Stockholm - Munich
    (8, 5),   # Edinburgh - Budapest
    (3, 7),   # Barcelona - Riga
    (8, 3),   # Edinburgh - Barcelona
    (9, 7),   # Vienna - Riga
    (3, 5),   # Barcelona - Budapest
    (0, 4),   # Bucharest - Warsaw
    (9, 1),   # Vienna - Krakow
    (8, 2),   # Edinburgh - Munich
    (3, 0),   # Barcelona - Bucharest
    (8, 7),   # Edinburgh - Riga
    (9, 6),   # Vienna - Stockholm
    (4, 1),   # Warsaw - Krakow
    (3, 1),   # Barcelona - Krakow
    (7, 2),   # Riga - Munich (explicitly given, treated bidirectionally)
    (9, 0),   # Vienna - Bucharest
    (5, 4),   # Budapest - Warsaw
    (9, 4),   # Vienna - Warsaw
    (3, 9),   # Barcelona - Vienna
    (5, 0),   # Budapest - Bucharest
    (9, 2),   # Vienna - Munich
    (7, 4),   # Riga - Warsaw
    (6, 7),   # Stockholm - Riga
    (6, 4)    # Stockholm - Warsaw
]

# Define a helper function for duration based on a city variable (using nested Ifs)
def duration_expr(city_var):
    return If(city_var == 0, durations[0],
           If(city_var == 1, durations[1],
           If(city_var == 2, durations[2],
           If(city_var == 3, durations[3],
           If(city_var == 4, durations[4],
           If(city_var == 5, durations[5],
           If(city_var == 6, durations[6],
           If(city_var == 7, durations[7],
           If(city_var == 8, durations[8],
           If(city_var == 9, durations[9],
           0)))))))))


# Define a function that creates a Z3 Boolean for allowed flights between two city variables
def allowed_flight(c1, c2):
    # Each allowed flight is bidirectional.
    constraints = []
    for (a, b) in allowed_flights:
        constraints.append(And(c1 == a, c2 == b))
        constraints.append(And(c1 == b, c2 == a))
    return Or(constraints)

def main():
    solver = Solver()

    num_cities = 10
    # pos[i]: city index at position i (0-indexed in the itinerary order)
    pos = [Int(f"pos_{i}") for i in range(num_cities)]
    # s[i]: start day for the city at position i
    s = [Int(f"s_{i}") for i in range(num_cities)]

    # Domain constraints for pos and s
    for i in range(num_cities):
        solver.add(pos[i] >= 0, pos[i] < num_cities)
        solver.add(s[i] >= 1, s[i] <= 32)

    # pos must form a permutation over the 10 cities.
    solver.add(Distinct(pos))

    # The itinerary spans exactly 32 days.
    # Note: If you fly from city A to city B on day X, day X is counted in both stays.
    # So the overall days = sum(durations) - (num_cities - 1) = 41 - 9 = 32.
    # We enforce the chaining: s[0] = 1 and for each i, s[i+1] = s[i] + duration(pos[i]) - 1, and final day equals 32.
    solver.add(s[0] == 1)
    for i in range(num_cities - 1):
        solver.add(s[i+1] == s[i] + duration_expr(pos[i]) - 1)
    solver.add(s[num_cities - 1] + duration_expr(pos[num_cities - 1]) - 1 == 32)

    # Enforce direct flight constraints on consecutive cities.
    for i in range(num_cities - 1):
        solver.add(allowed_flight(pos[i], pos[i+1]))

    # Add individual city time constraints based on requirements:
    for i in range(num_cities):
        # Munich (index 2): 3 days and must attend a workshop between day 18 and day 20.
        # This is enforced by requiring its start day be between 16 and 20 (so its days s, s+1, s+2 cover at least one of 18,19,20).
        solver.add(Implies(pos[i] == 2, And(s[i] >= 16, s[i] <= 20)))
        # Warsaw (index 4): 5 days and must attend a conference on day 25 and day 29.
        # For a 5-day stay to cover both 25 and 29, it must start on day 25.
        solver.add(Implies(pos[i] == 4, s[i] == 25))
        # Budapest (index 5): 5 days and the annual show runs day 9 to 13.
        # To cover the entire show (5 days), it must start on day 9.
        solver.add(Implies(pos[i] == 5, s[i] == 9))
        # Stockholm (index 6): 2 days and meet friends between day 17 and 18.
        # Thus its start day must be 16, 17, or 18 so that one of the days is within 17-18.
        solver.add(Implies(pos[i] == 6, Or(s[i] == 16, s[i] == 17, s[i] == 18)))
        # Edinburgh (index 8): 5 days and meet a friend between day 1 and 5.
        # It must start on or before day 5.
        solver.add(Implies(pos[i] == 8, s[i] <= 5))
        # For the other cities (Bucharest, Krakow, Barcelona, Riga, Vienna), their durations are fixed by durations dict.

    # Try to solve the constraints.
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for i in range(num_cities):
            city_idx = model.evaluate(pos[i]).as_long()
            start_day = model.evaluate(s[i]).as_long()
            end_day = start_day + durations[city_idx] - 1
            itinerary.append({
                "day_range": f"Day {start_day}-{end_day}",
                "place": cities[city_idx]
            })
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        # If no model is found, output an empty itinerary.
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()