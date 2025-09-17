from z3 import *
import json

def main():
    # City indices
    Nice = 0
    Dublin = 1
    Krakow = 2
    Lyon = 3
    Frankfurt = 4
    
    # Required days per city
    req = [5, 7, 6, 4, 2]
    
    # Direct flights
    connections = [
        (Nice, Dublin),
        (Dublin, Frankfurt),
        (Dublin, Krakow),
        (Krakow, Frankfurt),
        (Lyon, Frankfurt),
        (Nice, Frankfurt),
        (Lyon, Dublin),
        (Nice, Lyon)
    ]
    
    solver = Solver()
    
    # Segment city variables
    s2 = Int('s2')
    s3 = Int('s3')
    s4 = Int('s4')
    
    # Constraints: cities must be Dublin, Krakow, or Lyon and distinct
    solver.add(And(s2 >= 1, s2 <= 3))
    solver.add(And(s3 >= 1, s3 <= 3))
    solver.add(And(s4 >= 1, s4 <= 3))
    solver.add(Distinct(s2, s3, s4))
    
    # Connection check function
    def is_connected(c1, c2):
        return Or([And(c1 == a, c2 == b) for a, b in connections] + [And(c1 == b, c2 == a) for a, b in connections])
    
    # Flight constraints
    solver.add(is_connected(Nice, s2))
    solver.add(is_connected(s2, s3))
    solver.add(is_connected(s3, s4))
    solver.add(is_connected(s4, Frankfurt))
    
    if solver.check() == sat:
        model = solver.model()
        s2_val = model[s2].as_long()
        s3_val = model[s3].as_long()
        s4_val = model[s4].as_long()
        
        city_names = ['Nice', 'Dublin', 'Krakow', 'Lyon', 'Frankfurt']
        
        e2 = 4 + req[s2_val]
        e3 = 3 + req[s2_val] + req[s3_val]
        
        itinerary = [
            {"day_range": "Day 1-5", "place": city_names[Nice]},
            {"day_range": f"Day 5-{e2}", "place": city_names[s2_val]},
            {"day_range": f"Day {e2}-{e3}", "place": city_names[s3_val]},
            {"day_range": f"Day {e3}-19", "place": city_names[s4_val]},
            {"day_range": "Day 19-20", "place": city_names[Frankfurt]}
        ]
        
        print(json.dumps({"itinerary": itinerary}))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()