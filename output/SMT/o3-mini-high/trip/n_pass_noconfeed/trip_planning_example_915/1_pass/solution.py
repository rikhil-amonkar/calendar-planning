#!/usr/bin/env python3
import json
from z3 import *

def get_duration(city):
    # City indices: 0: Bucharest, 1: Venice, 2: Prague, 3: Frankfurt, 4: Zurich, 5: Florence, 6: Tallinn
    return If(city == 0, 3,
           If(city == 1, 5,
           If(city == 2, 4,
           If(city == 3, 5,
           If(city == 4, 5,
           If(city == 5, 5,
           If(city == 6, 5, 0)))))))

def main():
    s = Solver()
    
    # There are 7 cities
    n = 7
    # Order variables: a permutation of city indices {0,...,6}
    order = [Int(f"order_{i}") for i in range(n)]
    # Start day for each city in the itinerary (arrival day)
    start = [Int(f"start_{i}") for i in range(n)]
    
    # City names for later output.
    city_names = ["Bucharest", "Venice", "Prague", "Frankfurt", "Zurich", "Florence", "Tallinn"]
    
    # Domain constraints for order and start days.
    for i in range(n):
        s.add(order[i] >= 0, order[i] <= 6)
        s.add(start[i] >= 1, start[i] <= 26)
        
    # Ensure the order is a permutation.
    s.add(Distinct(order))
    
    # The trip starts on day 1.
    s.add(start[0] == 1)
    
    # If you spend L days in a city, and then fly on the last day (which counts in both cities),
    # then for city at position i, its "end" day is: start[i] + L - 1.
    # And the next city's start day must equal that end day (the shared flight day).
    for i in range(n - 1):
        s.add(start[i+1] == start[i] + (get_duration(order[i]) - 1))
        
    # Total trip duration must be 26 days.
    s.add(start[n-1] + get_duration(order[n-1]) - 1 == 26)
    
    # Allowed direct flights (interpreting "A and B" as bidirectional,
    # except "from Zurich to Florence" which is one-directional).
    allowed_flights = [
        (2, 6), (6, 2),            # Prague and Tallinn
        (2, 4), (4, 2),            # Prague and Zurich
        (5, 2), (2, 5),            # Florence and Prague
        (3, 0), (0, 3),            # Frankfurt and Bucharest
        (3, 1), (1, 3),            # Frankfurt and Venice
        (2, 0), (0, 2),            # Prague and Bucharest
        (0, 4), (4, 0),            # Bucharest and Zurich
        (6, 3), (3, 6),            # Tallinn and Frankfurt
        (4, 5),                   # from Zurich to Florence (only one direction)
        (3, 4), (4, 3),            # Frankfurt and Zurich
        (4, 1), (1, 4),            # Zurich and Venice
        (5, 3), (3, 5),            # Florence and Frankfurt
        (2, 3), (3, 2),            # Prague and Frankfurt
        (6, 4), (4, 6)             # Tallinn and Zurich
    ]
    
    # For each consecutive pair in the itinerary, enforce that a direct flight exists.
    for i in range(n - 1):
        flight_opts = []
        for (a, b) in allowed_flights:
            flight_opts.append(And(order[i] == a, order[i+1] == b))
        s.add(Or(flight_opts))
    
    # Event constraints:
    # 1. Wedding in Venice (city 1) between day 22 and day 26.
    #    The stay in Venice is [s, s+4] (since duration is 5 days).
    #    To have an overlap with [22,26], we need s+4 >= 22.
    for i in range(n):
        s.add(Implies(order[i] == 1, start[i] + 4 >= 22))
    # (Note: if Venice is scheduled on day 18 then its interval is Day 18-22, just including day 22.)
    
    # 2. Annual show in Frankfurt (city 3) from day 12 to day 16.
    #    Frankfurt has duration 5 so its interval is [s, s+4].
    #    To catch the show, we require s <= 16 and s+4 >= 12.
    for i in range(n):
        s.add(Implies(order[i] == 3, And(start[i] <= 16, start[i] + 4 >= 12)))
    
    # 3. Meeting with friends in Tallinn (city 6) between day 8 and day 12.
    #    Tallinn has duration 5 so its interval is [s, s+4].
    #    To have an overlap with [8,12], we require s <= 12 and s+4 >= 8.
    for i in range(n):
        s.add(Implies(order[i] == 6, And(start[i] <= 12, start[i] + 4 >= 8)))
    
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(n):
            city_index = m.evaluate(order[i]).as_long()
            s_day = m.evaluate(start[i]).as_long()
            dur = {0: 3, 1: 5, 2: 4, 3: 5, 4: 5, 5: 5, 6: 5}[city_index]
            end_day = s_day + dur - 1
            itinerary.append({
                "day_range": f"Day {s_day}-{end_day}",
                "place": city_names[city_index]
            })
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()