from z3 import *
import json

def main():
    # City indices: 0: Amsterdam, 1: Vienna, 2: Santorini, 3: Lyon
    cities = ["Amsterdam", "Vienna", "Santorini", "Lyon"]
    # Duration for each city
    duration_map = {0: 3, 1: 7, 2: 4, 3: 3}
    
    s = Solver()
    
    # Create decision variables for the itinerary order (a permutation of 4 cities)
    r0, r1, r2, r3 = Ints('r0 r1 r2 r3')
    s.add(And(r0 >= 0, r0 <= 3))
    s.add(And(r1 >= 0, r1 <= 3))
    s.add(And(r2 >= 0, r2 <= 3))
    s.add(And(r3 >= 0, r3 <= 3))
    s.add(Distinct(r0, r1, r2, r3))
    
    # Function returning the duration of a city given its index variable
    def d_expr(x):
        return If(x == 0, 3, If(x == 1, 7, If(x == 2, 4, If(x == 3, 3, 0))))
    
    # Timeline:
    # Let S0 be the start day of the first segment (fixed to day 1)
    # For a city visited in a segment, if its duration is D, then its segment covers days [S, S+D-1],
    # and if we fly on the last day of the segment then that day is shared with the next city.
    S0 = 1
    S1 = d_expr(r0)         # S1 = S0 + d(r0) - 1 (arrival day of segment2)
    S2 = S1 + d_expr(r1) - 1  # arrival day of segment3
    S3 = S2 + d_expr(r2) - 1  # arrival day of segment4
    End = S3 + d_expr(r3) - 1 # overall trip end day
    
    # Total trip must be 14 days.
    s.add(End == 14)
    
    # Allowed direct flights between cities.
    # Direct flights are available between:
    # Vienna and Lyon, Vienna and Santorini, Vienna and Amsterdam,
    # Amsterdam and Santorini, and Lyon and Amsterdam.
    # We assume flights are bidirectional.
    def allowed(x, y):
        return Or(
            And(x == 0, y == 1), And(x == 1, y == 0),  # Amsterdam <-> Vienna
            And(x == 0, y == 2), And(x == 2, y == 0),  # Amsterdam <-> Santorini
            And(x == 0, y == 3), And(x == 3, y == 0),  # Amsterdam <-> Lyon
            And(x == 1, y == 2), And(x == 2, y == 1),  # Vienna <-> Santorini
            And(x == 1, y == 3), And(x == 3, y == 1)   # Vienna <-> Lyon
        )
    
    # Enforce that consecutive cities in the order must be connected by a direct flight.
    s.add(allowed(r0, r1))
    s.add(allowed(r1, r2))
    s.add(allowed(r2, r3))
    
    # Event constraints:
    # - Workshop in Amsterdam (city 0) must occur between day 9 and day 11.
    #   If Amsterdam is visited in a segment starting at S, then that segment [S, S+dur-1] must cover at least one day in [9,11].
    #   This is encoded by: S <= 11 and S + (3 - 1) >= 9.
    s.add(Implies(r0 == 0, And(S0 <= 11, S0 + 2 >= 9)))
    s.add(Implies(r1 == 0, And(S1 <= 11, S1 + 2 >= 9)))
    s.add(Implies(r2 == 0, And(S2 <= 11, S2 + 2 >= 9)))
    s.add(Implies(r3 == 0, And(S3 <= 11, S3 + 2 >= 9)))
    
    # - Wedding in Lyon (city 3) must occur between day 7 and day 9.
    #   If Lyon is visited in a segment starting at S, then we require S <= 9 and S + (3 - 1) >= 7.
    s.add(Implies(r0 == 3, And(S0 <= 9, S0 + 2 >= 7)))
    s.add(Implies(r1 == 3, And(S1 <= 9, S1 + 2 >= 7)))
    s.add(Implies(r2 == 3, And(S2 <= 9, S2 + 2 >= 7)))
    s.add(Implies(r3 == 3, And(S3 <= 9, S3 + 2 >= 7)))
    
    # Solve the constraints
    if s.check() == sat:
        m = s.model()
        order = [m[r0].as_long(), m[r1].as_long(), m[r2].as_long(), m[r3].as_long()]
        
        # Compute the calendar day ranges for each segment
        seg_starts = []
        seg_ends = []
        
        start_day = 1
        # Segment 1
        seg_starts.append(start_day)
        end_day = start_day + duration_map[order[0]] - 1
        seg_ends.append(end_day)
        # For segments 2 to 4, the flight day is shared (overlap)
        for i in range(1, 4):
            start_day = end_day  # overlapping day
            seg_starts.append(start_day)
            end_day = start_day + duration_map[order[i]] - 1
            seg_ends.append(end_day)
        
        # Build the itinerary output list
        itinerary = []
        for i in range(4):
            itinerary.append({
                "day_range": "Day {}-{}".format(seg_starts[i], seg_ends[i]),
                "place": cities[order[i]]
            })
        
        result = {"itinerary": itinerary}
    else:
        result = {"itinerary": []}
    
    print(json.dumps(result))
    
if __name__ == '__main__':
    main()