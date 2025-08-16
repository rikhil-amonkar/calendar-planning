from z3 import *
import json

def main():
    s = Solver()
    
    # There are 8 cities (0..7) with fixed durations:
    # 0: Reykjavik (duration 2 days; must include a meeting day between day 3 and 4)
    # 1: Stockholm (duration 2 days; must include a meeting day between day 4 and 5)
    # 2: Porto (duration 5 days; wedding happens in Porto between day 13 and 17 -> segment must cover at least one day in [13,17])
    # 3: Nice (duration 3 days)
    # 4: Venice (duration 4 days)
    # 5: Vienna (duration 3 days; workshop must occur between day 11 and 13—even though we model it as a constraint on the start day)
    # 6: Split (duration 3 days)
    # 7: Copenhagen (duration 2 days)
    durations = [2, 2, 5, 3, 4, 3, 3, 2]
    city_names = {0:"Reykjavik", 1:"Stockholm", 2:"Porto", 3:"Nice", 4:"Venice", 5:"Vienna", 6:"Split", 7:"Copenhagen"}
    
    num_segments = 8
    # perm[i] = index of the city visited in the i-th segment 
    perm = [Int("p_%d" % i) for i in range(num_segments)]
    # S[i] = the calendar day on which segment i starts.
    S = [Int("S_%d" % i) for i in range(num_segments)]
    
    # Permutation constraints: each segment uses a distinct city (0..7)
    for i in range(num_segments):
        s.add(And(perm[i] >= 0, perm[i] < 8))
    s.add(Distinct(perm))
    
    # The itinerary is exactly 17 calendar days.
    # When you fly from one city to the next, the flight day is counted in both cities.
    # If segment i has duration d then its segment covers days S[i]... (S[i] + d - 1)
    # Also, by the chaining rule:
    #    S[0] = 1 
    # and for each i from 0 to 6: S[i+1] = S[i] + (duration of segment i) - 1.
    s.add(S[0] == 1)
    for i in range(num_segments - 1):
        # Use a piecewise definition for the duration of segment i:
        d_i = Sum([If(perm[i] == c, durations[c], 0) for c in range(8)])
        s.add(S[i+1] == S[i] + d_i - 1)
    # The end day of the last segment is S[7] + duration - 1 and must equal 17.
    last_duration = Sum([If(perm[7] == c, durations[c], 0) for c in range(8)])
    s.add(S[7] + last_duration - 1 == 17)
    
    # Event constraints for specific cities:
    # When visiting Reykjavik (0, duration 2) the 2‑day visit must include day 3 or 4.
    # In a 2–day segment starting on day S, the covered days are S and S+1.
    # So we force: if segment city is Reykjavik then S must be 2, 3, or 4.
    for i in range(num_segments):
        s.add(Implies(perm[i] == 0, Or(S[i] == 2, S[i] == 3, S[i] == 4)))
        
    # Similarly, Stockholm (1, duration 2): must cover a day in {4,5} 
    # i.e. possible start days: 3 (covers 3,4), 4 (covers 4,5), or 5 (covers 5,6)
    for i in range(num_segments):
        s.add(Implies(perm[i] == 1, Or(S[i] == 3, S[i] == 4, S[i] == 5)))
    
    # Porto (2, duration 5): must include a wedding day in [13,17]. 
    # Its covered days are S and S+1,...,S+4 so we require that at least one of these is in [13,17].
    # A sufficient (and simpler) way is to force S in [9, 13] so that S+4 is at least 13.
    for i in range(num_segments):
        s.add(Implies(perm[i] == 2, And(S[i] >= 9, S[i] <= 13)))
    
    # Vienna (5, duration 3): must include a workshop day between day 11 and 13.
    # Its days are S, S+1, S+2 so we force S to be between 9 and 13 (since 9,10,11,12,13 are the only possible start days that yield an intersection with [11,13])
    for i in range(num_segments):
        s.add(Implies(perm[i] == 5, And(S[i] >= 9, S[i] <= 13)))
    
    # Define the allowed direct flight pairs. (We assume flights work in both directions.)
    # The given flights are:
    #  • Copenhagen <–> Vienna      (7,5)
    #  • Nice <–> Stockholm         (3,1)
    #  • Split <–> Copenhagen         (6,7)
    #  • Nice <–> Reykjavik          (3,0)
    #  • Nice <–> Porto              (3,2)
    #  • Reykjavik <–> Vienna        (0,5)
    #  • Stockholm <–> Copenhagen    (1,7)
    #  • Nice <–> Venice             (3,4)
    #  • Nice <–> Vienna             (3,5)
    #  • Reykjavik <–> Copenhagen    (0,7)
    #  • Nice <–> Copenhagen         (3,7)
    #  • Stockholm <–> Vienna        (1,5)
    #  • Venice <–> Vienna           (4,5)
    #  • Copenhagen <–> Porto        (7,2)
    #  • Reykjavik <–> Stockholm     (0,1)
    #  • Stockholm <–> Split         (1,6)
    #  • Split <–> Vienna            (6,5)
    #  • Copenhagen <–> Venice       (7,4)
    #  • Vienna <–> Porto            (5,2)
    allowed_flights = [
         (7,5), (5,7),
         (3,1), (1,3),
         (6,7), (7,6),
         (3,0), (0,3),
         (3,2), (2,3),
         (0,5), (5,0),
         (1,7), (7,1),
         (3,4), (4,3),
         (3,5), (5,3),
         (3,7), (7,3),
         (1,5), (5,1),
         (4,5), (5,4),
         (7,2), (2,7),
         (0,1), (1,0),
         (1,6), (6,1),
         (6,5), (5,6),
         (7,4), (4,7),
         (5,2), (2,5)
    ]
    
    # For each consecutive pair of segments we require that there is a direct flight.
    for i in range(num_segments - 1):
        flight_allowed = []
        for (a, b) in allowed_flights:
            flight_allowed.append(And(perm[i] == a, perm[i+1] == b))
        s.add(Or(flight_allowed))
    
    # Solve the constraints.
    if s.check() == sat:
        m = s.model()
        # Retrieve the permutation (the order of visited cities) and starting days S.
        perm_sol = [m.evaluate(perm[i]).as_long() for i in range(num_segments)]
        S_sol = [m.evaluate(S[i]).as_long() for i in range(num_segments)]
        
        # For each segment, compute its end day.
        segments = []
        for i in range(num_segments):
            city = perm_sol[i]
            d_val = durations[city]
            start = S_sol[i]
            end = start + d_val - 1
            segments.append((city, start, end))
        
        # Build a day-to-place mapping for days 1..17.
        # Note that if a flight occurs on day d (that is, if d is the start day of a segment i>0),
        # then day d will be contained in two segments (the one ending and the one starting).
        # We will output a string with the two city names separated by "/".
        day_map = {}
        for day in range(1, 18):
            cities_here = []
            for (city, start, end) in segments:
                if start <= day <= end:
                    cities_here.append(city_names[city])
            day_map[day] = "/".join(cities_here)
        
        # Create the final itinerary list: one mapping per day.
        itinerary = []
        for day in range(1, 18):
            itinerary.append({"day": day, "place": day_map[day]})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=4))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()