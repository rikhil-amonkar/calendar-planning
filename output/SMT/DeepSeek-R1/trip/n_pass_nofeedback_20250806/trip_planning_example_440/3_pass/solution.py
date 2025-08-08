from z3 import *
import json

def main():
    # Represent cities as integers
    cities = ["Split", "Helsinki", "Reykjavik", "Vilnius", "Geneva"]
    Split, Helsinki, Reykjavik, Vilnius, Geneva = range(5)
    
    # Durations for each city
    durations = {
        Split: 2,
        Helsinki: 2,
        Reykjavik: 3,
        Vilnius: 3,
        Geneva: 6
    }
    
    # Direct flight connections (bidirectional)
    allowed_pairs = set()
    connections = [
        (Split, Helsinki),
        (Geneva, Split),
        (Geneva, Helsinki),
        (Helsinki, Reykjavik),
        (Vilnius, Helsinki),
        (Split, Vilnius)
    ]
    for a, b in connections:
        allowed_pairs.add((a, b))
        allowed_pairs.add((b, a))
    
    # Position variables for the order of cities
    pos = IntVector('pos', 5)
    s = Solver()
    
    # Each city must be an integer between 0-4
    for i in range(5):
        s.add(pos[i] >= 0, pos[i] < 5)
    
    # Each city appears exactly once
    s.add(Distinct(pos))
    
    # Start day variables
    start = IntVector('start', 5)
    s.add(start[0] == 1)
    
    # Calculate consecutive start days
    for i in range(4):
        s.add(start[i+1] == start[i] + durations[pos[i]] - 1)
    s.add(start[4] + durations[pos[4]] - 1 == 12)
    
    # Consecutive cities must have direct flights
    for i in range(4):
        s.add(Or(*[(pos[i] == a) & (pos[i+1] == b) for (a, b) in allowed_pairs]))
    
    # Event constraints
    for i in range(5):
        # Reykjavik must have at least one day between 10-12
        s.add(If(pos[i] == Reykjavik, 
                 And(start[i] <= 10, start[i] + durations[Reykjavik] - 1 >= 10),
                 True))
        # Vilnius must have at least one day between 7-9
        s.add(If(pos[i] == Vilnius, 
                 And(start[i] <= 9, start[i] + durations[Vilnius] - 1 >= 7),
                 True))
    
    # Solve and output itinerary
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(5):
            city_index = m.evaluate(pos[i]).as_long()
            city_name = cities[city_index]
            st_day = m.evaluate(start[i]).as_long()
            # Add each day in the city's stay
            for day in range(st_day, st_day + durations[city_index]):
                itinerary.append({"day": day, "place": city_name})
        print(json.dumps({"itinerary": itinerary}, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()