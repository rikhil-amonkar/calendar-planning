from z3 import *
import json

def main():
    s = Solver()
    
    # City mapping: 0-Valencia, 1-Athens, 2-Naples, 3-Zurich
    s1 = Int('s1')
    s2 = Int('s2')
    s3 = Int('s3')
    s4 = Int('s4')
    
    s.add(s1 >= 0, s1 <= 3)
    s.add(s2 >= 0, s2 <= 3)
    s.add(s3 >= 0, s3 <= 3)
    s.add(s4 >= 0, s4 <= 3)
    s.add(Distinct(s1, s2, s3, s4))
    
    days_list = [6, 6, 5, 6]
    
    e1 = Int('e1')
    e2 = Int('e2')
    e3 = Int('e3')
    
    s.add(e1 == days_list[s1])
    s.add(e2 == e1 + days_list[s2] - 1)
    s.add(e3 == e2 + days_list[s3] - 1)
    s.add(e3 == 21 - days_list[s4])
    
    s.add(e1 >= 1, e1 <= 20)
    s.add(e2 >= e1, e2 <= 20)
    s.add(e3 >= e2, e3 <= 20)
    
    # Athens constraints
    s.add(If(s2 == 1, e1 <= 6, True))
    s.add(If(s3 == 1, e2 <= 6, True))
    s.add(If(s4 == 1, e3 <= 6, True))
    
    # Naples constraints
    s.add(If(s1 == 2, e1 >= 16, True))
    s.add(If(s2 == 2, And(e1 <= 20, e2 >= 16), True))
    s.add(If(s3 == 2, And(e2 <= 20, e3 >= 16), True))
    
    if s.check() == sat:
        model = s.model()
        s1_val = model[s1].as_long()
        s2_val = model[s2].as_long()
        s3_val = model[s3].as_long()
        s4_val = model[s4].as_long()
        e1_val = model[e1].as_long()
        e2_val = model[e2].as_long()
        e3_val = model[e3].as_long()
        
        city_names = {0: "Valencia", 1: "Athens", 2: "Naples", 3: "Zurich"}
        
        itinerary = [
            {"day_range": f"Day 1-{e1_val}", "place": city_names[s1_val]},
            {"day_range": f"Day {e1_val}-{e2_val}", "place": city_names[s2_val]},
            {"day_range": f"Day {e2_val}-{e3_val}", "place": city_names[s3_val]},
            {"day_range": f"Day {e3_val}-20", "place": city_names[s4_val]}
        ]
        
        print(json.dumps({"itinerary": itinerary}))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()