from z3 import Int, Solver, And, Or, Distinct, sat
import json

def main():
    # City mapping: 0 -> Vilnius, 1 -> Munich, 2 -> Mykonos
    city_names = {0: "Vilnius", 1: "Munich", 2: "Mykonos"}
    days_required = {0: 4, 1: 3, 2: 7}
    
    # Direct flights: symmetric connections
    def has_direct_flight(a, b):
        return Or(
            And(a == 0, b == 1),
            And(a == 1, b == 0),
            And(a == 1, b == 2),
            And(a == 2, b == 1)
        )
    
    # Z3 variables for the three segments
    city1 = Int('city1')
    city2 = Int('city2')
    city3 = Int('city3')
    
    s = Solver()
    # Each city must be 0, 1, or 2
    s.add(city1 >= 0, city1 <= 2)
    s.add(city2 >= 0, city2 <= 2)
    s.add(city3 >= 0, city3 <= 2)
    # All segments must be distinct cities
    s.add(Distinct(city1, city2, city3))
    # Flight connections between consecutive segments
    s.add(has_direct_flight(city1, city2))
    s.add(has_direct_flight(city2, city3))
    
    if s.check() == sat:
        model = s.model()
        c1 = model[city1].as_long()
        c2 = model[city2].as_long()
        c3 = model[city3].as_long()
        
        # Calculate non-travel days per segment
        s1 = days_required[c1] - 1
        s2 = days_required[c2] - 2
        s3 = days_required[c3] - 1
        
        # Calculate day ranges
        end1 = s1 + 1
        end2 = end1 + s2 + 1
        start2 = end1
        start3 = end2
        
        itinerary = [
            {"day_range": f"Day 1-{end1}", "place": city_names[c1]},
            {"day_range": f"Day {start2}-{end2}", "place": city_names[c2]},
            {"day_range": f"Day {start3}-12", "place": city_names[c3]}
        ]
        
        print(json.dumps({"itinerary": itinerary}))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()