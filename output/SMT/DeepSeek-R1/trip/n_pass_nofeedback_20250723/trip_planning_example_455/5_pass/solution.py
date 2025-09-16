from z3 import *
import json

def main():
    # Cities mapping: 0-Reykjavik, 1-Riga, 2-Warsaw, 3-Istanbul, 4-Krakow
    city_names = {
        0: "Reykjavik",
        1: "Riga",
        2: "Warsaw",
        3: "Istanbul",
        4: "Krakow"
    }
    dur_req = [7, 2, 3, 6, 7]  # durations for cities 0,1,2,3,4

    # Allowed direct flights as undirected edges
    allowed_edges = [
        (0, 2), (2, 0),  # Reykjavik <-> Warsaw
        (1, 2), (2, 1),  # Riga <-> Warsaw
        (1, 3), (3, 1),  # Riga <-> Istanbul
        (2, 3), (3, 2),  # Warsaw <-> Istanbul
        (2, 4), (4, 2),  # Warsaw <-> Krakow
        (3, 4), (4, 3)   # Istanbul <-> Krakow
    ]

    # Create Z3 solver
    s = Solver()
    
    # Order of cities (0-4 for each position)
    order = [Int(f'o{i}') for i in range(5)]
    for i in range(5):
        s.add(order[i] >= 0, order[i] <= 4)
    s.add(Distinct(order))
    
    # Start and end days for each city
    starts = [Int(f'start_{i}') for i in range(5)]
    ends = [Int(f'end_{i}') for i in range(5)]
    
    # Constrain days to be within 1-21 and maintain sequence
    s.add(starts[0] == 1)
    for i in range(4):
        s.add(starts[i+1] == ends[i] + 1)  # Overnight flight to next city
    s.add(ends[4] == 21)
    
    # Ensure end >= start for each city
    for i in range(5):
        s.add(ends[i] >= starts[i])
        duration = ends[i] - starts[i] + 1
        
        # Fixed duration constraints using Or/And
        city = order[i]
        s.add(Or(
            And(city == 0, duration == dur_req[0]),
            And(city == 1, duration == dur_req[1]),
            And(city == 2, duration == dur_req[2]),
            And(city == 3, duration == dur_req[3]),
            And(city == 4, duration == dur_req[4])
        ))
    
    # Flight constraints between consecutive cities
    for i in range(4):
        city1 = order[i]
        city2 = order[i+1]
        s.add(Or(
            And(city1 == 0, city2 == 2),
            And(city1 == 2, city2 == 0),
            And(city1 == 1, city2 == 2),
            And(city1 == 2, city2 == 1),
            And(city1 == 1, city2 == 3),
            And(city1 == 3, city2 == 1),
            And(city1 == 2, city2 == 3),
            And(city1 == 3, city2 == 2),
            And(city1 == 2, city2 == 4),
            And(city1 == 4, city2 == 2),
            And(city1 == 3, city2 == 4),
            And(city1 == 4, city2 == 3)
        ))
    
    # Event constraints
    for i in range(5):
        city = order[i]
        start = starts[i]
        end = ends[i]
        # Riga must include at least one of day 1 or 2
        s.add(Implies(city == 1, And(start <= 2, end >= 1)))
        # Istanbul must include at least one day between day 2 and 7
        s.add(Implies(city == 3, And(start <= 7, end >= 2)))
    
    if s.check() == sat:
        m = s.model()
        order_vals = [m[o].as_long() for o in order]
        start_vals = [m[s].as_long() for s in starts]
        end_vals = [m[e].as_long() for e in ends]
        
        # Build itinerary per day
        itinerary = []
        for day in range(1, 22):
            places = []
            for i in range(5):
                if day >= start_vals[i] and day <= end_vals[i]:
                    places.append(city_names[order_vals[i]])
            itinerary.append({"day": day, "place": places})
        
        print(json.dumps({"itinerary": itinerary}, indent=2))
    else:
        print("No solution found")

if __name__ == '__main__':
    main()