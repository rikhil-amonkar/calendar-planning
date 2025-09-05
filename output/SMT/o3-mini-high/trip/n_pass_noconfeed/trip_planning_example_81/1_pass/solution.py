#!/usr/bin/env python3
from z3 import *
import json

def main():
    # Total calendar days
    num_days = 9
    # Cities: 0 = Mykonos, 1 = Budapest, 2 = Hamburg
    city_names = ["Mykonos", "Budapest", "Hamburg"]

    # Create a solver instance
    s = Solver()

    # Create city variables for each day: c[0] corresponds to Day 1, …, c[8] to Day 9.
    c = [Int(f"c{i+1}") for i in range(num_days)]
    for day in range(num_days):
        s.add(Or(c[day] == 0, c[day] == 1, c[day] == 2))
    
    # Create flight decision variables for Days 2..9.
    # f_vars[d] is True if a direct flight is taken on calendar day d.
    f_vars = {}
    for d in range(2, num_days+1):
        f_vars[d] = Bool(f"f{d}")
    
    # Allowed direct flight transitions.
    # A flight from A to B is allowed if:
    #   Mykonos (0) <-> Budapest (1) and Budapest (1) <-> Hamburg (2)
    def allowed_transition(a, b):
        return Or(And(a == 0, b == 1),
                  And(a == 1, b == 0),
                  And(a == 1, b == 2),
                  And(a == 2, b == 1))
    
    # Transition constraints for day 2 to day 9.
    # For each day d (2..9): if a flight is taken on day d then the city changes
    # (and the flight must be allowed) otherwise the city stays the same.
    for d in range(2, num_days+1):
        # In our list, c[d-2] is Day (d-1)'s city and c[d-1] is Day d's city.
        s.add(If(f_vars[d],
                 And(c[d-2] != c[d-1], allowed_transition(c[d-2], c[d-1])),
                 c[d-1] == c[d-2]))
    
    # Conference constraints:
    # On Day 4 and Day 9 you must be in Mykonos.
    # If a flight is taken on that day, then either the departure or arrival city must be Mykonos.
    # Day 4: if f_vars[4] is True then (c[2] or c[3]) must be Mykonos (0), else c[3] must equal 0.
    if 4 in f_vars:
        s.add(If(f_vars[4], Or(c[2] == 0, c[3] == 0), c[3] == 0))
    else:
        s.add(c[3] == 0)
    # Day 9: if f_vars[9] is True then (c[7] or c[8]) must be Mykonos, else c[8] must equal 0.
    if 9 in f_vars:
        s.add(If(f_vars[9], Or(c[7] == 0, c[8] == 0), c[8] == 0))
    else:
        s.add(c[8] == 0)
    
    # Count the total days spent in each city.
    # Note: On Day 1, you are only in c[0]. For a day d >= 2:
    # if a flight is taken on day d, then both the previous city (c[d-2]) and current city (c[d-1])
    # are counted for that day; otherwise, only the current city (c[d-1]) gets a day.
    count_M = If(c[0] == 0, 1, 0)
    count_B = If(c[0] == 1, 1, 0)
    count_H = If(c[0] == 2, 1, 0)
    for d in range(2, num_days+1):
        count_M += If(f_vars[d],
                      (If(c[d-2] == 0, 1, 0) + If(c[d-1] == 0, 1, 0)),
                      If(c[d-1] == 0, 1, 0))
        count_B += If(f_vars[d],
                      (If(c[d-2] == 1, 1, 0) + If(c[d-1] == 1, 1, 0)),
                      If(c[d-1] == 1, 1, 0))
        count_H += If(f_vars[d],
                      (If(c[d-2] == 2, 1, 0) + If(c[d-1] == 2, 1, 0)),
                      If(c[d-1] == 2, 1, 0))
    
    s.add(count_M == 6)  # Mykonos for 6 days
    s.add(count_B == 3)  # Budapest for 3 days
    s.add(count_H == 2)  # Hamburg for 2 days

    # Total number of flights must be exactly 2 because each flight day adds one extra city-day.
    flight_count = Sum([If(f_vars[d], 1, 0) for d in range(2, num_days+1)])
    s.add(flight_count == 2)

    # Solve the constraints
    if s.check() == sat:
        m = s.model()
        # Get city assignment for each calendar day (Day 1 to Day 9)
        day_cities = [m.evaluate(c[day]).as_long() for day in range(num_days)]
        # Get list of flight days (those days on which a flight is taken)
        flight_days = [d for d in range(2, num_days+1) if is_true(m.evaluate(f_vars[d]))]
        
        # Build itinerary segments.
        # The convention is that if a flight is taken on day X then day X is shared by two segments:
        # the segment ending on day X (departure city) and the segment starting on day X (arrival city).
        segments = []
        if not flight_days:
            # No flights taken => one continuous segment.
            segments.append({"day_range": f"Day 1-{num_days}", "place": city_names[day_cities[0]]})
        else:
            # First segment: from Day 1 to the first flight day uses the initial city.
            first_flight = flight_days[0]
            segments.append({"day_range": f"Day 1-{first_flight}", "place": city_names[day_cities[0]]})
            # For each flight day, the segment starting at that day uses the flight's arrival city.
            for idx in range(len(flight_days)):
                start_day = flight_days[idx]
                # The arrival city on the flight day is captured by c[start_day-1] (since day indexes start at 1)
                arrival_city = m.evaluate(c[start_day - 1]).as_long()
                if idx + 1 < len(flight_days):
                    end_day = flight_days[idx+1]
                else:
                    end_day = num_days
                segments.append({"day_range": f"Day {start_day}-{end_day}", "place": city_names[arrival_city]})
        
        result = {"itinerary": segments}
        print(json.dumps(result))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()