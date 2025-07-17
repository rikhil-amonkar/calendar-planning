from z3 import *
import json

def main():
    s1, s2, s3 = Ints('s1 s2 s3')
    a, b = Ints('a b')
    s = Solver()
    
    s.add(Distinct(s1, s2, s3))
    s.add(s1 >= 0, s1 <= 2)
    s.add(s2 >= 0, s2 <= 2)
    s.add(s3 >= 0, s3 <= 2)
    
    s.add(a >= 1, a < 10)
    s.add(b > a, b <= 10)
    
    s.add(If(s1 == 0, a == 2, True))
    s.add(If(s1 == 1, a == 4, True))
    s.add(If(s1 == 2, a == 6, True))
    
    s.add(If(s2 == 0, b - a + 1 == 2, True))
    s.add(If(s2 == 1, b - a + 1 == 4, True))
    s.add(If(s2 == 2, b - a + 1 == 6, True))
    
    s.add(If(s3 == 0, 10 - b + 1 == 2, True))
    s.add(If(s3 == 1, 10 - b + 1 == 4, True))
    s.add(If(s3 == 2, 10 - b + 1 == 6, True))
    
    s.add(Or(
        And(s1 == 2, a >= 5),
        And(s2 == 2, b >= 5),
        s3 == 2
    ))
    
    s.add(Or(
        And(s1 == 0, s2 == 1),
        And(s1 == 1, s2 == 0),
        And(s1 == 1, s2 == 2),
        And(s1 == 2, s2 == 1)
    ))
    
    s.add(Or(
        And(s2 == 0, s3 == 1),
        And(s2 == 1, s3 == 0),
        And(s2 == 1, s3 == 2),
        And(s2 == 2, s3 == 1)
    ))
    
    if s.check() == sat:
        m = s.model()
        a_val = m[a].as_long()
        b_val = m[b].as_long()
        s1_val = m[s1].as_long()
        s2_val = m[s2].as_long()
        s3_val = m[s3].as_long()
        
        city_map = {0: "Mykonos", 1: "Vienna", 2: "Venice"}
        city1 = city_map[s1_val]
        city2 = city_map[s2_val]
        city3 = city_map[s3_val]
        
        itinerary = [
            {"day_range": "Day 1-{}".format(a_val), "place": city1},
            {"day_range": "Day {}".format(a_val), "place": city1},
            {"day_range": "Day {}".format(a_val), "place": city2},
            {"day_range": "Day {}-{}".format(a_val, b_val), "place": city2},
            {"day_range": "Day {}".format(b_val), "place": city2},
            {"day_range": "Day {}".format(b_val), "place": city3},
            {"day_range": "Day {}-10".format(b_val), "place": city3}
        ]
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()