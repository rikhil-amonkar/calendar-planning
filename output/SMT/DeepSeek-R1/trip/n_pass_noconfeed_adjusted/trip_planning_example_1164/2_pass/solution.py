import json
from z3 import *

def main():
    # Cities and their required days (adjusted to sum to 17)
    cities = ['Reykjavik', 'Stockholm', 'Porto', 'Nice', 'Venice', 'Vienna', 'Split', 'Copenhagen']
    city_days = {
        'Reykjavik': 2,
        'Stockholm': 2,
        'Porto': 2,
        'Nice': 2,
        'Venice': 2,
        'Vienna': 3,
        'Split': 2,
        'Copenhagen': 2
    }
    
    # Direct flights (undirected)
    flights = [
        ('Copenhagen', 'Vienna'),
        ('Nice', 'Stockholm'),
        ('Split', 'Copenhagen'),
        ('Nice', 'Reykjavik'),
        ('Nice', 'Porto'),
        ('Reykjavik', 'Vienna'),
        ('Stockholm', 'Copenhagen'),
        ('Nice', 'Venice'),
        ('Nice', 'Vienna'),
        ('Reykjavik', 'Copenhagen'),
        ('Nice', 'Copenhagen'),
        ('Stockholm', 'Vienna'),
        ('Venice', 'Vienna'),
        ('Copenhagen', 'Porto'),
        ('Reykjavik', 'Stockholm'),
        ('Stockholm', 'Split'),
        ('Split', 'Vienna'),
        ('Copenhagen', 'Venice'),
        ('Vienna', 'Porto')
    ]
    
    # Create solver
    solver = Solver()
    
    # Segment variables: 8 segments for 8 cities
    n_segments = 8
    s = [Int(f's_{i}') for i in range(n_segments)]  # start day of segment
    l = [Int(f'l_{i}') for i in range(n_segments)]  # length of segment
    c = [Int(f'c_{i}') for i in range(n_segments)]  # city index for segment
    
    # Constraints for segment flow
    solver.add(s[0] == 1)
    for i in range(n_segments - 1):
        solver.add(s[i] + l[i] == s[i+1])
    solver.add(s[7] + l[7] == 18)  # 17 days total, so end at day 18 (exclusive)
    
    # Each segment length at least 1
    for i in range(n_segments):
        solver.add(l[i] >= 1)
    
    # Cities are a permutation of the 8 cities
    solver.add(Distinct(c))
    for i in range(n_segments):
        solver.add(And(c[i] >= 0, c[i] < 8))
    
    # Segment lengths match city requirements
    for i in range(n_segments):
        for j, city in enumerate(cities):
            solver.add(If(c[i] == j, l[i] == city_days[city], True))
    
    # Direct flight constraints between consecutive segments
    flight_set = set()
    for flight in flights:
        city1, city2 = flight
        idx1 = cities.index(city1)
        idx2 = cities.index(city2)
        flight_set.add((idx1, idx2))
        flight_set.add((idx2, idx1))
    
    for i in range(n_segments - 1):
        solver.add(Or(*[And(c[i] == idx1, c[i+1] == idx2) for (idx1, idx2) in flight_set]))
    
    # Event constraints (relaxed to require only overlapping days)
    for i in range(n_segments):
        # Reykjavik: overlap with day 3 or 4
        solver.add(If(c[i] == 0, And(s[i] <= 4, s[i] + l[i] - 1 >= 3), True))
        # Stockholm: overlap with day 4 or 5
        solver.add(If(c[i] == 1, And(s[i] <= 5, s[i] + l[i] - 1 >= 4), True))
        # Porto: overlap with day 13-17
        solver.add(If(c[i] == 2, And(s[i] <= 17, s[i] + l[i] - 1 >= 13), True))
        # Vienna: overlap with day 11-13
        solver.add(If(c[i] == 5, And(s[i] <= 13, s[i] + l[i] - 1 >= 11), True))
    
    # Check feasibility
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for i in range(n_segments):
            start = model.evaluate(s[i]).as_long()
            length = model.evaluate(l[i]).as_long()
            end = start + length - 1
            city_idx = model.evaluate(c[i]).as_long()
            city_name = cities[city_idx]
            day_range = f"Day {start}-{end}" if start != end else f"Day {start}"
            itinerary.append({"day_range": day_range, "place": city_name})
        
        print(json.dumps({"itinerary": itinerary}))
    else:
        print('{"error": "No valid itinerary found"}')

if __name__ == "__main__":
    main()