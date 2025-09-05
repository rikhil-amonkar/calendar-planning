from z3 import *
import json

def main():
    solver = Solver()
    
    num_cities = 9
    # Define decision variables for the itinerary order, arrival days (s) and departure days (f)
    order = [Int(f"order_{i}") for i in range(num_cities)]
    s = [Int(f"s_{i}") for i in range(num_cities)]
    f_day = [Int(f"f_{i}") for i in range(num_cities)]
    
    # Mapping of indices to city names
    cities = [
        "Santorini",  # index 0
        "Krakow",     # index 1
        "Paris",      # index 2
        "Vilnius",    # index 3
        "Munich",     # index 4
        "Geneva",     # index 5
        "Amsterdam",  # index 6
        "Budapest",   # index 7
        "Split"       # index 8
    ]
    # Durations (in days) for each city visit
    # Note: day X counts for both departing and arriving city if a flight occurs.
    # So the "overlapped" flight days mean total distinct days = sum(durations) - (num_cities-1) = 38 - 8 = 30.
    durations = {
        0: 5,  # Santorini
        1: 5,  # Krakow
        2: 5,  # Paris
        3: 3,  # Vilnius
        4: 5,  # Munich
        5: 2,  # Geneva
        6: 4,  # Amsterdam
        7: 5,  # Budapest
        8: 4   # Split
    }
    
    # Allowed direct flight connections.
    # Most flights are bidirectional except those specified "from".
    allowed_edges = [
        (2, 1), (1, 2),      # Paris <-> Krakow
        (2, 6), (6, 2),      # Paris <-> Amsterdam
        (2, 8), (8, 2),      # Paris <-> Split
        (3, 4),             # Vilnius -> Munich (only direction allowed)
        (2, 5), (5, 2),      # Paris <-> Geneva
        (6, 5), (5, 6),      # Amsterdam <-> Geneva
        (4, 8), (8, 4),      # Munich <-> Split
        (8, 1), (1, 8),      # Split <-> Krakow
        (4, 6), (6, 4),      # Munich <-> Amsterdam
        (7, 6), (6, 7),      # Budapest <-> Amsterdam
        (8, 5), (5, 8),      # Split <-> Geneva
        (3, 8), (8, 3),      # Vilnius <-> Split
        (4, 5), (5, 4),      # Munich <-> Geneva
        (4, 1), (1, 4),      # Munich <-> Krakow
        (1, 3),             # Krakow -> Vilnius (only direction allowed)
        (3, 6), (6, 3),      # Vilnius <-> Amsterdam
        (7, 2), (2, 7),      # Budapest <-> Paris
        (1, 6), (6, 1),      # Krakow <-> Amsterdam
        (3, 2), (2, 3),      # Vilnius <-> Paris
        (7, 5), (5, 7),      # Budapest <-> Geneva
        (8, 6), (6, 8),      # Split <-> Amsterdam
        (0, 5), (5, 0),      # Santorini <-> Geneva
        (6, 0), (0, 6),      # Amsterdam <-> Santorini
        (4, 7), (7, 4),      # Munich <-> Budapest
        (4, 2), (2, 4)       # Munich <-> Paris
    ]
    
    # Domain constraints: Each city index is between 0 and num_cities-1, days are within 1..30.
    for i in range(num_cities):
        solver.add(order[i] >= 0, order[i] < num_cities)
        solver.add(s[i] >= 1)
        solver.add(f_day[i] <= 30)
        
    # Ensure each city is visited exactly once.
    solver.add(Distinct(order))
    
    # Overall itinerary time span constraints.
    solver.add(s[0] == 1)
    solver.add(f_day[num_cities - 1] == 30)
    
    # If you fly from city A to city B on a day X then that day is counted for both cities.
    # Hence, the departure day of a city equals the arrival day of the next city.
    for i in range(num_cities - 1):
        solver.add(s[i+1] == f_day[i])
    
    # Duration constraints: f_day[i] = s[i] + (duration - 1)
    for i in range(num_cities):
        solver.add(f_day[i] == 
            If(order[i] == 0, s[i] + 5 - 1,       # Santorini: 5 days
            If(order[i] == 1, s[i] + 5 - 1,         # Krakow: 5 days
            If(order[i] == 2, s[i] + 5 - 1,         # Paris: 5 days
            If(order[i] == 3, s[i] + 3 - 1,         # Vilnius: 3 days
            If(order[i] == 4, s[i] + 5 - 1,         # Munich: 5 days
            If(order[i] == 5, s[i] + 2 - 1,         # Geneva: 2 days
            If(order[i] == 6, s[i] + 4 - 1,         # Amsterdam: 4 days
            If(order[i] == 7, s[i] + 5 - 1,         # Budapest: 5 days
            If(order[i] == 8, s[i] + 4 - 1, s[i]))))))))))
    
    # Flight transitions: Consecutive cities in the itinerary must have a direct flight.
    for i in range(num_cities - 1):
        allowed_transition = []
        for (a, b) in allowed_edges:
            allowed_transition.append(And(order[i] == a, order[i+1] == b))
        solver.add(Or(allowed_transition))
    
    # Special event constraints:
    # Santorini: Must meet friends between day 25 and day 29.
    # That is, the stay (which is 5 days) must cover at least one day between 25 and 29.
    for i in range(num_cities):
        solver.add(If(order[i] == 0, And(s[i] <= 29, f_day[i] >= 25), True))
        # Krakow: Wedding between day 18 and day 22.
        solver.add(If(order[i] == 1, And(s[i] <= 22, f_day[i] >= 18), True))
        # Paris: Meet friend between day 11 and day 15.
        solver.add(If(order[i] == 2, And(s[i] <= 15, f_day[i] >= 11), True))
    
    # Check if the constraints are satisfiable and retrieve the model.
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for i in range(num_cities):
            city_index = model.evaluate(order[i]).as_long()
            start_day = model.evaluate(s[i]).as_long()
            end_day = model.evaluate(f_day[i]).as_long()
            itinerary.append({
                "day_range": f"Day {start_day}-{end_day}",
                "place": cities[city_index]
            })
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        # If no itinerary satisfies the constraints, output an empty itinerary.
        print(json.dumps({"itinerary": []}))
        
if __name__ == "__main__":
    main()