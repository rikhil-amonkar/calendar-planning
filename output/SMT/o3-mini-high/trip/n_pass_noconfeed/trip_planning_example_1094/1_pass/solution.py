from z3 import *
import json

def main():
    # Define cities and their fixed durations
    cities = ["Vienna", "Barcelona", "Edinburgh", "Krakow", "Riga", "Hamburg", "Paris", "Stockholm"]
    # Durations: Vienna:4, Barcelona:2, Edinburgh:4, Krakow:3, Riga:4, Hamburg:2, Paris:2, Stockholm:2
    durations_list = [4, 2, 4, 3, 4, 2, 2, 2]
    
    # Create a Z3 solver instance
    solver = Solver()
    
    # We have 8 segments corresponding to an ordering (itinerary) of the 8 cities.
    # itin[i] is an integer (0..7) representing the city visited in the i-th segment.
    itin = [Int("itin_%d" % i) for i in range(8)]
    for i in range(8):
        solver.add(itin[i] >= 0, itin[i] <= 7)
    solver.add(Distinct(itin))
    
    # s[i] will represent the starting day for the i-th segment.
    s_vars = [Int("s_%d" % i) for i in range(8)]
    for i in range(8):
        solver.add(s_vars[i] >= 1, s_vars[i] <= 16)
    
    # Define a helper function to return the duration (number of days) for a given city (by its index)
    def duration(city):
        return If(city == 0, 4,
               If(city == 1, 2,
               If(city == 2, 4,
               If(city == 3, 3,
               If(city == 4, 4,
               If(city == 5, 2,
               If(city == 6, 2,
               If(city == 7, 2, 0))))))))
    
    # The travel model uses the idea that if you fly from city A to city B on day X,
    # you count day X both in A and in B. Thus, for the itinerary segments we have:
    # s[0] = 1, and for each segment i=0..6:
    #   s[i+1] = s[i] + (duration(itin[i]) - 1)
    solver.add(s_vars[0] == 1)
    for i in range(7):
        solver.add(s_vars[i+1] == s_vars[i] + (duration(itin[i]) - 1))
    # The final day must be day 16. The last segment covers days s[7] to s[7] + duration(itin[7]) - 1.
    solver.add(s_vars[7] + duration(itin[7]) - 1 == 16)
    
    # Allowed direct flight connections between cities (unordered pairs).
    allowed_pairs = [
        (0,1),  # Vienna - Barcelona
        (0,3),  # Vienna - Krakow
        (0,4),  # Vienna - Riga
        (0,5),  # Vienna - Hamburg
        (0,6),  # Vienna - Paris (via Paris-Vienna)
        (0,7),  # Vienna - Stockholm
        (1,3),  # Barcelona - Krakow
        (1,4),  # Barcelona - Riga
        (1,5),  # Barcelona - Hamburg
        (1,6),  # Barcelona - Paris
        (1,7),  # Barcelona - Stockholm
        (2,3),  # Edinburgh - Krakow
        (2,4),  # Edinburgh - Riga
        (2,5),  # Edinburgh - Hamburg
        (2,6),  # Edinburgh - Paris
        (2,7),  # Edinburgh - Stockholm
        (3,6),  # Krakow - Paris
        (3,7),  # Krakow - Stockholm
        (4,5),  # Riga - Hamburg
        (4,6),  # Riga - Paris (via Paris-Riga)
        (4,7),  # Riga - Stockholm
        (5,6),  # Hamburg - Paris
        (5,7),  # Hamburg - Stockholm
        (6,7)   # Paris - Stockholm
    ]
    
    # For each consecutive pair of cities in the itinerary, add flight constraints.
    for i in range(7):
        a = itin[i]
        b = itin[i+1]
        allowed_flight = []
        for (x, y) in allowed_pairs:
            allowed_flight.append(Or(And(a == x, b == y), And(a == y, b == x)))
        solver.add(Or(allowed_flight))
    
    # Add event constraints:
    # 1. Wedding in Paris between Day 1 and Day 2:
    #    If the city in a segment is Paris (index 6), then its starting day must be 1 or 2 (so that [s, s+1] includes day 1 or 2).
    for i in range(8):
        solver.add(If(itin[i] == 6, s_vars[i] <= 2, True))
    
    # 2. Conference in Hamburg on Day 10 and Day 11:
    #    Hamburg (index 5) is 2 days long; to cover days 10 and 11 it must start on day 10.
    for i in range(8):
        solver.add(If(itin[i] == 5, s_vars[i] == 10, True))
    
    # 3. Meeting friend in Edinburgh between Day 12 and Day 15:
    #    Edinburgh (index 2) is 4 days long, so its segment [s, s+3] must include some day in [12,15].
    #    A sufficient condition is: s <= 15 and s+3 >= 12, i.e. s in [9,15].
    for i in range(8):
        solver.add(If(itin[i] == 2, And(s_vars[i] >= 9, s_vars[i] <= 15), True))
    
    # 4. Visit relatives in Stockholm between Day 15 and Day 16:
    #    Stockholm (index 7) is 2 days long so its segment [s, s+1] must include a day in [15,16].
    #    This is satisfied if s is either 14 or 15. We enforce s between 14 and 15.
    for i in range(8):
        solver.add(If(itin[i] == 7, And(s_vars[i] >= 14, s_vars[i] <= 15), True))
    
    # Check for satisfiability and build the itinerary output.
    if solver.check() == sat:
        m = solver.model()
        itinerary_result = []
        for i in range(8):
            city_index = m.evaluate(itin[i]).as_long()
            start_day = m.evaluate(s_vars[i]).as_long()
            dur = durations_list[city_index]
            end_day = start_day + dur - 1
            itinerary_result.append({
                "day_range": f"Day {start_day}-{end_day}",
                "place": cities[city_index]
            })
        print(json.dumps({"itinerary": itinerary_result}))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()