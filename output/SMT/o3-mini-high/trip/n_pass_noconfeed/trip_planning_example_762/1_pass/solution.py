#!/usr/bin/env python3
from z3 import *
import json

# Returns the required duration for a given city (represented symbolically)
def get_duration(city):
    # City IDs: 0: Dublin, 1: Madrid, 2: Oslo, 3: London, 4: Vilnius, 5: Berlin
    return If(city == 0, 3,
           If(city == 1, 2,
           If(city == 2, 3,
           If(city == 3, 2,
           If(city == 4, 3, 5)))))

def main():
    s = Solver()
    n = 6  # number of cities/segments
    
    # Permutation: each position gets a city id in {0,1,2,3,4,5}
    perm = [Int(f"city_{i}") for i in range(n)]
    # s_i: the start day (in the itinerary) for the visit at position i.
    start = [Int(f"s_{i}") for i in range(n)]
    
    # Domain constraints for permutation variables (each city appears exactly once)
    for i in range(n):
        s.add(perm[i] >= 0, perm[i] < n)
    s.add(Distinct(perm))
    
    # Define the itinerary structure with flight days overlapping:
    # The first city must be entered on Day 1.
    s.add(start[0] == 1)
    for i in range(n - 1):
        # When leaving a city, you fly on the last day of that city’s visit,
        # so the next city is entered on the same day (counted as a day in both cities).
        s.add(start[i + 1] == start[i] + get_duration(perm[i]) - 1)
    # The trip lasts exactly 13 days (computed as last city's end day)
    s.add(start[n - 1] + get_duration(perm[n - 1]) - 1 == 13)
    
    # Event constraints: require that specific events fall within the visit span.
    for i in range(n):
        # Dublin (ID 0): spend 3 days and meet friends between day 7 and 9 
        s.add(If(perm[i] == 0,
                 And(start[i] <= 9, start[i] + 3 - 1 >= 7),
                 True))
        # Madrid (ID 1): spend 2 days and visit relatives between day 2 and 3 
        s.add(If(perm[i] == 1,
                 And(start[i] <= 3, start[i] + 2 - 1 >= 2),
                 True))
        # Berlin (ID 5): spend 5 days and attend a wedding between day 3 and 7
        s.add(If(perm[i] == 5,
                 And(start[i] <= 7, start[i] + 5 - 1 >= 3),
                 True))
        # No additional event constraints for Oslo (2), London (3) or Vilnius (4)
    
    # Flight connectivity constraints:
    # Allowed direct flights (bidirectional) between cities:
    # (London, Madrid), (Oslo, Vilnius), (Berlin, Vilnius), (Madrid, Oslo),
    # (Madrid, Dublin), (London, Oslo), (Madrid, Berlin), (Berlin, Oslo),
    # (Dublin, Oslo), (London, Dublin), (London, Berlin), (Berlin, Dublin)
    #
    # Using our city ID mapping:
    # Dublin: 0, Madrid: 1, Oslo: 2, London: 3, Vilnius: 4, Berlin: 5
    allowed_pairs = [(3, 1), (2, 4), (5, 4), (1, 2), (1, 0), 
                     (3, 2), (1, 5), (5, 2), (0, 2), (3, 0),
                     (3, 5), (5, 0)]
    
    for i in range(n - 1):
        A = perm[i]
        B = perm[i + 1]
        options = []
        for (p, q) in allowed_pairs:
            # Allow flight in either direction
            options.append(And(A == p, B == q))
            options.append(And(A == q, B == p))
        s.add(Or(options))
    
    if s.check() == sat:
        m = s.model()
        itinerary = []
        # Mapping from city ID to city name and fixed duration
        city_names = {0: "Dublin", 1: "Madrid", 2: "Oslo", 3: "London", 4: "Vilnius", 5: "Berlin"}
        fixed_durations = {0: 3, 1: 2, 2: 3, 3: 2, 4: 3, 5: 5}
        for i in range(n):
            city_id = m.evaluate(perm[i]).as_long()
            day_start = m.evaluate(start[i]).as_long()
            dur = fixed_durations[city_id]
            day_end = day_start + dur - 1
            itinerary.append({"day_range": f"Day {day_start}-{day_end}", "place": city_names[city_id]})
        output = {"itinerary": itinerary}
    else:
        output = {"itinerary": []}
    
    print(json.dumps(output))
    
if __name__ == "__main__":
    main()