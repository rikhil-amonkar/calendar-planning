import json
from z3 import *

def main():
    # There are 8 cities with fixed durations:
    # 0: Dublin: 5 days (must be exactly from Day 11 to Day 15)
    # 1: Krakow: 4 days
    # 2: Istanbul: 3 days (must include at least one day between Day 9 and Day 11)
    # 3: Venice: 3 days
    # 4: Naples: 4 days
    # 5: Brussels: 2 days
    # 6: Mykonos: 4 days (must have at least one day between Day 1 and Day 4)
    # 7: Frankfurt: 3 days (must include at least one day between Day 15 and Day 17)
    #
    # Total "city days" = 28, but the itinerary timeline (with shared flight days) is 21 days.
    #
    # We structure the itinerary as 8 segments. For segments 0..7:
    #   s[i]: the starting day of segment i
    #   e[i]: the ending day of segment i
    # For the first segment, s[0] = 1.
    # For subsequent segments, s[i] = e[i-1] (the flight day is shared).
    # Each segment i has length d[i] = e[i] - s[i] + 1.
    # The fixed durations for the city in segment i are given by:
    #   if city == Dublin then d[i] = 5, etc.
    # And we require e[7] = 21.
    
    # Direct flight connections (bidirectional) are allowed only between:
    # Dublin <-> Brussels, Mykonos <-> Naples, Venice <-> Istanbul,
    # Frankfurt <-> Krakow, Naples <-> Dublin, Krakow <-> Brussels,
    # Naples <-> Istanbul, Naples <-> Brussels, Istanbul <-> Frankfurt,
    # Brussels <-> Frankfurt, Istanbul <-> Krakow, Istanbul <-> Brussels,
    # Venice <-> Frankfurt, Naples <-> Frankfurt, Dublin <-> Krakow,
    # Venice <-> Brussels, Naples <-> Venice, Istanbul <-> Dublin,
    # Venice <-> Dublin, Dublin <-> Frankfurt.
    
    num_segments = 8
    city_names = {
        0: "Dublin",
        1: "Krakow",
        2: "Istanbul",
        3: "Venice",
        4: "Naples",
        5: "Brussels",
        6: "Mykonos",
        7: "Frankfurt"
    }
    # Fixed durations for each city:
    durations_const = {
        0: 5,
        1: 4,
        2: 3,
        3: 3,
        4: 4,
        5: 2,
        6: 4,
        7: 3
    }
    
    solver = Solver()

    # Decision variables:
    # order[i] indicates the city visited in segment i (an integer in 0..7)
    order = [Int(f"order_{i}") for i in range(num_segments)]
    # s[i] is the starting day for segment i and e[i] is the ending day for segment i.
    s_vars = [Int(f"s_{i}") for i in range(num_segments)]
    e_vars = [Int(f"e_{i}") for i in range(num_segments)]
    
    # Domain and distinctness for order
    for i in range(num_segments):
        solver.add(order[i] >= 0, order[i] < num_segments)
    solver.add(Distinct(order))
    
    # Define each segment's duration based on the city chosen.
    def duration(i):
        # duration of segment i depends on order[i]
        return If(order[i] == 0, durations_const[0],
               If(order[i] == 1, durations_const[1],
               If(order[i] == 2, durations_const[2],
               If(order[i] == 3, durations_const[3],
               If(order[i] == 4, durations_const[4],
               If(order[i] == 5, durations_const[5],
               If(order[i] == 6, durations_const[6],
               If(order[i] == 7, durations_const[7], 0)))))))
    
    # Timeline constraints: segments are contiguous with a shared flight day.
    solver.add(s_vars[0] == 1)
    solver.add(e_vars[0] == s_vars[0] + duration(0) - 1)
    for i in range(1, num_segments):
        solver.add(s_vars[i] == e_vars[i-1])
        solver.add(e_vars[i] == s_vars[i] + duration(i) - 1)
    solver.add(e_vars[num_segments - 1] == 21)
    
    # Special schedule constraints:
    # Dublin must be exactly from Day 11 to Day 15.
    for i in range(num_segments):
        solver.add(Implies(order[i] == 0, And(s_vars[i] == 11, e_vars[i] == 15)))
        
    # Istanbul: Meet friend between Day 9 and Day 11 (segment must cover at least one day in [9,11])
    for i in range(num_segments):
        solver.add(Implies(order[i] == 2, And(s_vars[i] <= 11, e_vars[i] >= 9)))
    
    # Mykonos: Visit relatives between Day 1 and Day 4 (segment must start on or before Day 4)
    for i in range(num_segments):
        solver.add(Implies(order[i] == 6, s_vars[i] <= 4))
    
    # Frankfurt: Meet friends between Day 15 and Day 17 (segment must cover at least one day in [15,17])
    for i in range(num_segments):
        solver.add(Implies(order[i] == 7, And(s_vars[i] <= 17, e_vars[i] >= 15)))
    
    # Flight connectivity constraints: Only allowed direct flights between consecutive segments.
    def allowed_flight(c1, c2):
        return Or(
            And(c1 == 0, c2 == 5), And(c1 == 5, c2 == 0),  # Dublin <-> Brussels
            And(c1 == 6, c2 == 4), And(c1 == 4, c2 == 6),  # Mykonos <-> Naples
            And(c1 == 3, c2 == 2), And(c1 == 2, c2 == 3),  # Venice <-> Istanbul
            And(c1 == 7, c2 == 1), And(c1 == 1, c2 == 7),  # Frankfurt <-> Krakow
            And(c1 == 4, c2 == 0), And(c1 == 0, c2 == 4),  # Naples <-> Dublin
            And(c1 == 1, c2 == 5), And(c1 == 5, c2 == 1),  # Krakow <-> Brussels
            And(c1 == 4, c2 == 2), And(c1 == 2, c2 == 4),  # Naples <-> Istanbul
            And(c1 == 4, c2 == 5), And(c1 == 5, c2 == 4),  # Naples <-> Brussels
            And(c1 == 2, c2 == 7), And(c1 == 7, c2 == 2),  # Istanbul <-> Frankfurt
            And(c1 == 5, c2 == 7), And(c1 == 7, c2 == 5),  # Brussels <-> Frankfurt
            And(c1 == 2, c2 == 1), And(c1 == 1, c2 == 2),  # Istanbul <-> Krakow
            And(c1 == 2, c2 == 5), And(c1 == 5, c2 == 2),  # Istanbul <-> Brussels
            And(c1 == 3, c2 == 7), And(c1 == 7, c2 == 3),  # Venice <-> Frankfurt
            And(c1 == 4, c2 == 7), And(c1 == 7, c2 == 4),  # Naples <-> Frankfurt
            And(c1 == 0, c2 == 1), And(c1 == 1, c2 == 0),  # Dublin <-> Krakow
            And(c1 == 3, c2 == 5), And(c1 == 5, c2 == 3),  # Venice <-> Brussels
            And(c1 == 2, c2 == 0), And(c1 == 0, c2 == 2),  # Istanbul <-> Dublin
            And(c1 == 3, c2 == 0), And(c1 == 0, c2 == 3),  # Venice <-> Dublin
            And(c1 == 0, c2 == 7), And(c1 == 7, c2 == 0)   # Dublin <-> Frankfurt
        )
    
    for i in range(num_segments - 1):
        solver.add(allowed_flight(order[i], order[i+1]))
    
    # Find a solution and build the JSON itinerary.
    if solver.check() == sat:
        m = solver.model()
        itinerary = []
        seg_order = [m.evaluate(order[i]).as_long() for i in range(num_segments)]
        seg_start = [m.evaluate(s_vars[i]).as_long() for i in range(num_segments)]
        seg_end = [m.evaluate(e_vars[i]).as_long() for i in range(num_segments)]
        for i in range(num_segments):
            itinerary.append({
                "day_range": f"Day {seg_start[i]}-{seg_end[i]}",
                "place": city_names[seg_order[i]]
            })
        print(json.dumps({"itinerary": itinerary}))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()