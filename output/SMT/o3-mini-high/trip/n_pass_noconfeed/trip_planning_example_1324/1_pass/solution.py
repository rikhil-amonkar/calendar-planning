from z3 import *
import json

def duration_constraint(city, a, d):
    # Returns the constraint that the duration (d - a + 1) equals the required days
    return If(city == 0, d - a + 1 == 4,         # Venice: 4 days
           If(city == 1, d - a + 1 == 3,         # Barcelona: 3 days
           If(city == 2, d - a + 1 == 4,         # Copenhagen: 4 days
           If(city == 3, d - a + 1 == 4,         # Lyon: 4 days
           If(city == 4, d - a + 1 == 4,         # Reykjavik: 4 days
           If(city == 5, d - a + 1 == 5,         # Dubrovnik: 5 days
           If(city == 6, d - a + 1 == 2,         # Athens: 2 days
           If(city == 7, d - a + 1 == 5,         # Tallinn: 5 days
           If(city == 8, d - a + 1 == 3,         # Munich: 3 days
              True))))))))
    
def main():
    solver = Solver()
    num_cities = 9

    # Define integer variables for the order (route) and schedule (arrival and departure days)
    route = [Int("city_%d" % i) for i in range(num_cities)]
    arrival = [Int("arrival_%d" % i) for i in range(num_cities)]
    departure = [Int("departure_%d" % i) for i in range(num_cities)]

    # Constrain route to be a permutation of the 9 cities (encoded as 0..8)
    for i in range(num_cities):
        solver.add(route[i] >= 0, route[i] < num_cities)
    solver.add(Distinct(route))

    # Constrain each stay to have the required duration based on the city.
    for i in range(num_cities):
        solver.add(duration_constraint(route[i], arrival[i], departure[i]))
        solver.add(arrival[i] >= 1)
        solver.add(departure[i] <= 26)
    
    # Time-bound constraints:
    # Meet friend in Barcelona (ID 1) between day 10 and 12.
    for i in range(num_cities):
        solver.add(Implies(route[i] == 1, And(arrival[i] <= 12, departure[i] >= 10)))
    # Visit relatives in Copenhagen (ID 2) between day 7 and 10.
    for i in range(num_cities):
        solver.add(Implies(route[i] == 2, And(arrival[i] <= 10, departure[i] >= 7)))
    # Attend wedding in Dubrovnik (ID 5) between day 16 and 20.
    for i in range(num_cities):
        solver.add(Implies(route[i] == 5, And(arrival[i] <= 20, departure[i] >= 16)))
    
    # Link the days across the itinerary.
    # The trip starts on day 1.
    solver.add(arrival[0] == 1)
    # When flying, the departure day from city i equals the arrival day at city i+1.
    for i in range(1, num_cities):
        solver.add(arrival[i] == departure[i-1])
    # The trip ends on day 26.
    solver.add(departure[num_cities-1] == 26)

    # Define the allowed direct flights (assumed bidirectional).
    allowed_flights = [
        (2, 6),   # Copenhagen - Athens
        (2, 5),   # Copenhagen - Dubrovnik
        (8, 7),   # Munich - Tallinn
        (2, 8),   # Copenhagen - Munich
        (0, 8),   # Venice - Munich
        (4, 6),   # Reykjavik - Athens
        (6, 5),   # Athens - Dubrovnik
        (0, 6),   # Venice - Athens
        (3, 1),   # Lyon - Barcelona
        (2, 4),   # Copenhagen - Reykjavik
        (4, 8),   # Reykjavik - Munich
        (6, 8),   # Athens - Munich
        (3, 8),   # Lyon - Munich
        (1, 4),   # Barcelona - Reykjavik
        (0, 2),   # Venice - Copenhagen
        (1, 5),   # Barcelona - Dubrovnik
        (3, 0),   # Lyon - Venice
        (5, 8),   # Dubrovnik - Munich
        (1, 6),   # Barcelona - Athens
        (2, 1),   # Copenhagen - Barcelona
        (0, 1),   # Venice - Barcelona
        (1, 8),   # Barcelona - Munich
        (1, 7),   # Barcelona - Tallinn
        (2, 7)    # Copenhagen - Tallinn
    ]

    # Constrain the route transitions to only allow direct flights.
    for i in range(num_cities - 1):
        c1 = route[i]
        c2 = route[i+1]
        flight_possible = []
        for (a_val, b_val) in allowed_flights:
            flight_possible.append(And(c1 == a_val, c2 == b_val))
            flight_possible.append(And(c1 == b_val, c2 == a_val))
        solver.add(Or(*flight_possible))

    # Solve for a valid itinerary.
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        city_names = {
            0: "Venice",
            1: "Barcelona",
            2: "Copenhagen",
            3: "Lyon",
            4: "Reykjavik",
            5: "Dubrovnik",
            6: "Athens",
            7: "Tallinn",
            8: "Munich"
        }
        for i in range(num_cities):
            city_id = model[route[i]].as_long()
            start_day = model[arrival[i]].as_long()
            end_day = model[departure[i]].as_long()
            itinerary.append({
                "day_range": f"Day {start_day}-{end_day}",
                "place": city_names[city_id]
            })
        print(json.dumps({"itinerary": itinerary}))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()