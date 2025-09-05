from z3 import *
import json

def main():
    # Define city names and their required durations
    # City IDs: 0: Stuttgart, 1: Istanbul, 2: Vilnius, 3: Seville,
    # 4: Geneva, 5: Valencia, 6: Munich, 7: Reykjavik
    cities = {
        0: "Stuttgart",
        1: "Istanbul",
        2: "Vilnius",
        3: "Seville",
        4: "Geneva",
        5: "Valencia",
        6: "Munich",
        7: "Reykjavik"
    }
    durations = {
        0: 4,  # Stuttgart
        1: 4,  # Istanbul
        2: 4,  # Vilnius
        3: 3,  # Seville
        4: 5,  # Geneva
        5: 5,  # Valencia
        6: 3,  # Munich
        7: 4   # Reykjavik
    }
    
    # Allowed direct-flight transitions (ordered pairs).
    # For undirected connections we include both directions.
    # For the ones specified as "from", we only include the given direction.
    allowed_flights = [
        (4, 1), (1, 4),        # Geneva <-> Istanbul
        (7, 6), (6, 7),        # Reykjavik <-> Munich
        (0, 5), (5, 0),        # Stuttgart <-> Valencia
        (7, 0),                # Reykjavik -> Stuttgart only
        (0, 1), (1, 0),        # Stuttgart <-> Istanbul
        (6, 4), (4, 6),        # Munich <-> Geneva
        (1, 2), (2, 1),        # Istanbul <-> Vilnius
        (5, 3), (3, 5),        # Valencia <-> Seville
        (5, 1), (1, 5),        # Valencia <-> Istanbul
        (2, 6),                # Vilnius -> Munich only
        (3, 6), (6, 3),        # Seville <-> Munich
        (6, 1), (1, 6),        # Munich <-> Istanbul
        (5, 4), (4, 5),        # Valencia <-> Geneva
        (5, 6), (6, 5)         # Valencia <-> Munich
    ]
    
    # Create a Z3 solver instance
    solver = Solver()
    
    n = 8  # Total number of cities to visit
    # order[i] will denote the city visited in the i-th segment (0-indexed).
    order = [Int(f"order_{i}") for i in range(n)]
    # start[i] will be the starting day for the segment in which the city order[i] is visited.
    start = [Int(f"s_{i}") for i in range(n)]
    
    # Function to return the duration based on the city variable using piecewise if-then-else.
    def duration_expr(city):
        return If(city == 0, 4,
               If(city == 1, 4,
               If(city == 2, 4,
               If(city == 3, 3,
               If(city == 4, 5,
               If(city == 5, 5,
               If(city == 6, 3,
               If(city == 7, 4, 0))))))))
    
    # Add domain constraints for order and start days.
    for i in range(n):
        solver.add(order[i] >= 0, order[i] <= 7)
        solver.add(start[i] >= 1, start[i] <= 25)
    # Ensure each city is visited exactly once.
    solver.add(Distinct(order))
    
    # Recurrence constraints: if you stay in a city for a number of days, 
    # and you fly on the last day (which counts in both cities), then:
    # s[0] = 1 and for each segment, s[i+1] = s[i] + duration(order[i]) - 1.
    solver.add(start[0] == 1)
    for i in range(n - 1):
        solver.add(start[i+1] == start[i] + duration_expr(order[i]) - 1)
    
    # The last segment must end on day 25.
    solver.add(start[n-1] + duration_expr(order[n-1]) - 1 == 25)
    
    # Flight connectivity constraints: consecutive cities in the itinerary must be directly connected.
    for i in range(n - 1):
        flight_options = []
        for (a, b) in allowed_flights:
            flight_options.append(And(order[i] == a, order[i+1] == b))
        solver.add(Or(flight_options))
    
    # Event and time constraints for specific cities:
    for i in range(n):
        # Stuttgart: Stay 4 days. Must be in Stuttgart on day 4 and day 7.
        # For a 4-day stay, the only possibility is that s == 4 (covering days 4,5,6,7).
        solver.add(Implies(order[i] == 0, start[i] == 4))
        
        # Istanbul: Stay 4 days. Must visit relatives in Istanbul between day 19 and day 22.
        # For a 4-day stay (s, s+1, s+2, s+3) to cover an intersection with [19,22],
        # we require s <= 22 and s+3 >= 19, i.e., s >= 16 and s <= 22.
        solver.add(Implies(order[i] == 1, And(start[i] >= 16, start[i] <= 22)))
        
        # Vilnius: Desired 4-day visit (no extra event constraint).
        
        # Seville: Stay 3 days (no extra event constraint).
        
        # Geneva: Stay 5 days (no extra event constraint).
        
        # Valencia: Stay 5 days (no extra event constraint).
        
        # Munich: Stay 3 days and attend the annual show from day 13 to 15.
        # The only 3-day interval covering days 13, 14, and 15 is when s == 13.
        solver.add(Implies(order[i] == 6, start[i] == 13))
        
        # Reykjavik: Stay 4 days and attend a workshop between day 1 and day 4.
        # Its 4-day interval must intersect [1,4], ensuring start <= 4.
        solver.add(Implies(order[i] == 7, start[i] <= 4))
    
    # Check and solve the constraints.
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for i in range(n):
            city_id = model.eval(order[i]).as_long()
            city_name = cities[city_id]
            s_day = model.eval(start[i]).as_long()
            d = durations[city_id]
            e_day = s_day + d - 1
            itinerary.append({
                "day_range": f"Day {s_day}-{e_day}",
                "place": city_name
            })
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()