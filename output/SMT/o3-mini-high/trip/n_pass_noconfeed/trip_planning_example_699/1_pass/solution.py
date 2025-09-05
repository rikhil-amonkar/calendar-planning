from z3 import *
import json

def main():
    solver = Solver()
    
    # Define cities, their IDs and required durations.
    # IDs: 0: Hamburg, 1: Dublin, 2: Helsinki, 3: Reykjavik, 4: London, 5: Mykonos
    cities = {0: "Hamburg", 1: "Dublin", 2: "Helsinki", 3: "Reykjavik", 4: "London", 5: "Mykonos"}
    durations = {0: 2, 1: 5, 2: 4, 3: 2, 4: 5, 5: 3}
    n = 6  # Total number of cities
    
    # Create an array "order" where order[i] is the city id visited at position i.
    order = [Int("order_%d" % i) for i in range(n)]
    # Create an array S for the start day of the stay in the city at position i.
    S = [Int("S_%d" % i) for i in range(n)]
    
    # Domain constraints: each order[i] is between 0 and 5 and all must be distinct.
    for i in range(n):
        solver.add(And(order[i] >= 0, order[i] <= 5))
    solver.add(Distinct(order))
    
    # Fixed positions based on constraints:
    # Hamburg must be visited at the start to meet friends between Day 1-2.
    # Dublin must be visited as the second city, to exactly cover Day 2-6 (show period).
    solver.add(order[0] == 0)  # Hamburg (id 0)
    solver.add(order[1] == 1)  # Dublin (id 1)
    
    # Timeline: The trip starts on Day 1.
    solver.add(S[0] == 1)
    
    # Define a helper to express the duration of a city given its id (symbolic).
    def duration_expr(city_expr):
        return If(city_expr == 0, durations[0],
               If(city_expr == 1, durations[1],
               If(city_expr == 2, durations[2],
               If(city_expr == 3, durations[3],
               If(city_expr == 4, durations[4],
                  durations[5])))))
    
    # For consecutive segments, if you fly from city A (at position i) to city B (at position i+1),
    # then the flight day is counted in both. Therefore, we have:
    # S[0] = 1 and for i=0,...,4: S[i+1] = S[i] + duration(A) - 1.
    for i in range(n - 1):
        solver.add(S[i+1] == S[i] + duration_expr(order[i]) - 1)
    
    # The end day E for city at position i is: E[i] = S[i] + duration(city) - 1.
    # Total itinerary must cover Day 16. That is, the last city must end on Day 16.
    solver.add(S[n-1] + duration_expr(order[n-1]) - 1 == 16)
    
    # City-specific constraints:
    # Dublin (id 1) must be exactly Day 2-6.
    # With Hamburg (duration 2) at position 0, we have S[1] = 1 + 2 - 1 = 2,
    # making Dublin's interval [2, 2+5-1] = [2,6], which automatically meets the show constraint.
    
    # Reykjavik (id 3) must include the wedding which is between Day 9 and Day 10.
    # Since its duration is 2, if its start day is s then the interval is [s, s+1].
    # To include Day 9 or Day 10, s must be 8, 9, or 10.
    for i in range(n):
        solver.add(Implies(order[i] == 3, Or(S[i] == 8, S[i] == 9, S[i] == 10)))
    
    # Define the allowed direct flight connections (undirected).
    # Each pair (u,v) means there's a direct flight between city u and city v.
    allowed_edges = [(0, 1), (1, 4), (2, 3), (0, 4), (1, 2), 
                     (3, 4), (4, 5), (1, 3), (0, 2), (2, 4)]
    
    # For every consecutive pair of cities in the itinerary, enforce that a direct flight exists.
    for i in range(n - 1):
        a = order[i]
        b = order[i + 1]
        flight_allowed = []
        for (u, v) in allowed_edges:
            flight_allowed.append(Or(And(a == u, b == v), And(a == v, b == u)))
        solver.add(Or(flight_allowed))
    
    # Solve the SMT problem.
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for i in range(n):
            city_id = model[order[i]].as_long()
            start_day = model[S[i]].as_long()
            dur = durations[city_id]
            end_day = start_day + dur - 1
            itinerary.append({
                "day_range": "Day {}-{}".format(start_day, end_day),
                "place": cities[city_id]
            })
        output = {"itinerary": itinerary}
        print(json.dumps(output))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()