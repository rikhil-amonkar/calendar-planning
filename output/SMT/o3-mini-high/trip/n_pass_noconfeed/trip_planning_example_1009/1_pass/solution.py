#!/usr/bin/env python
from z3 import *
import json

def main():
    # Define cities and their required durations.
    cities = ["Riga", "Manchester", "Bucharest", "Florence", "Vienna", "Istanbul", "Reykjavik", "Stuttgart"]
    # Durations for each city (in days)
    durations = [4, 5, 4, 4, 2, 2, 4, 5]  # indices: 0: Riga, 1: Manchester, 2: Bucharest, 3: Florence, 4: Vienna, 5: Istanbul, 6: Reykjavik, 7: Stuttgart
    
    n = len(cities)  # 8 cities in total
    total_days = 23  # Overall trip days
    
    solver = Solver()
    
    # Permutation variables: order[i] will be the index of the city visited in position i.
    order = [Int("order_%d" % i) for i in range(n)]
    for i in range(n):
        solver.add(And(order[i] >= 0, order[i] < n))
    solver.add(Distinct(order))
    
    # Timeline: start[i] represents the starting day of the stay for the city at position i.
    starts = [Int("start_%d" % i) for i in range(n)]
    # Let's require that all start days are at least 1 and at most total_days.
    for s in starts:
        solver.add(s >= 1, s <= total_days)
    
    # Define an expression to get the duration for the city assigned at position i.
    def duration_expr(i):
        return If(order[i] == 0, durations[0],
               If(order[i] == 1, durations[1],
               If(order[i] == 2, durations[2],
               If(order[i] == 3, durations[3],
               If(order[i] == 4, durations[4],
               If(order[i] == 5, durations[5],
               If(order[i] == 6, durations[6],
               If(order[i] == 7, durations[7],
                  0)))))))
    
    # The trip starts on day 1.
    solver.add(starts[0] == 1)
    
    # For each city in the itinerary (except the last), the next city's start day is set to
    # the current city's end day (arriving by flight on the same day).
    # End day for a city = start day + duration - 1.
    for i in range(n - 1):
        solver.add(starts[i+1] == starts[i] + duration_expr(i) - 1)
    
    # The final city's end day must be total_days.
    solver.add(starts[n - 1] + duration_expr(n - 1) - 1 == total_days)
    
    # Allowed direct flights between cities (assumed bidirectional). Each tuple (a,b)
    # means there is a direct flight connection between cities with indices a and b.
    allowed_flights = [
        (2, 4), (4, 2),      # Bucharest and Vienna
        (6, 4), (4, 6),      # Reykjavik and Vienna
        (1, 4), (4, 1),      # Manchester and Vienna
        (1, 0), (0, 1),      # Manchester and Riga
        (0, 4), (4, 0),      # Riga and Vienna
        (5, 4), (4, 5),      # Istanbul and Vienna
        (4, 3), (3, 4),      # Vienna and Florence
        (7, 4), (4, 7),      # Stuttgart and Vienna
        (0, 2), (2, 0),      # Riga and Bucharest
        (5, 0), (0, 5),      # Istanbul and Riga
        (7, 5), (5, 7),      # Stuttgart and Istanbul
        (6, 7), (7, 6),      # Reykjavik and Stuttgart (from Reykjavik to Stuttgart, assumed bidirectional)
        (5, 2), (2, 5),      # Istanbul and Bucharest
        (1, 5), (5, 1),      # Manchester and Istanbul
        (1, 2), (2, 1),      # Manchester and Bucharest
        (7, 1), (1, 7)       # Stuttgart and Manchester
    ]
    
    # Add flight connectivity constraints between consecutive cities.
    for i in range(n - 1):
        possible_flights = []
        for (a, b) in allowed_flights:
            possible_flights.append(And(order[i] == a, order[i+1] == b))
        solver.add(Or(possible_flights))
    
    # Event Constraints:
    # 1. Bucharest workshop: The workshop in Bucharest (city index 2) must fall between day 16 and day 19.
    #    Since the stay in Bucharest lasts 4 days, its interval [start, start+3] must overlap with [16,19].
    #    That is equivalent to: start <= 19 and start+3 >= 16.
    for i in range(n):
        solver.add(Implies(order[i] == 2, And(starts[i] <= 19, starts[i] + 3 >= 16)))
    
    # 2. Istanbul annual show: The show in Istanbul (city index 5) is from day 12 to day 13.
    #    Istanbul is visited for 2 days, so its interval [start, start+1] must overlap with [12,13].
    #    That is: start <= 13 and start+1 >= 12.
    for i in range(n):
        solver.add(Implies(order[i] == 5, And(starts[i] <= 13, starts[i] + 1 >= 12)))
    
    # Solve the constraints
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for i in range(n):
            city_index = model[order[i]].as_long()
            start_day = model[starts[i]].as_long()
            d = durations[city_index]
            end_day = start_day + d - 1
            itinerary.append({
                "day_range": "Day {}-{}".format(start_day, end_day),
                "place": cities[city_index]
            })
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()