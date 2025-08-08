import json
from z3 import *

def main():
    cities = ["Krakow", "Frankfurt", "Dubrovnik", "Naples", "Oslo"]
    c0, c1, c2, c3 = Ints('c0 c1 c2 c3')
    s = Solver()

    s.add(c0 >= 0, c0 <= 3)
    s.add(c1 >= 0, c1 <= 3)
    s.add(c2 >= 0, c2 <= 3)
    s.add(c3 >= 0, c3 <= 3)
    s.add(Distinct(c0, c1, c2, c3))

    def dur(city):
        return If(city == 1, 4, 5)

    def adj(i, j):
        return Or(
            And(i == 0, j == 1),
            And(i == 1, j == 0),
            And(i == 1, j == 2),
            And(i == 2, j == 1),
            And(i == 1, j == 3),
            And(i == 3, j == 1),
            And(i == 2, j == 3),
            And(i == 3, j == 2)
        )
    
    s.add(adj(c0, c1))
    s.add(adj(c1, c2))
    s.add(adj(c2, c3))
    
    s0 = 1
    s1 = s0 + dur(c0) - 1
    s2 = s1 + dur(c1) - 1
    s3 = s2 + dur(c2) - 1
    
    s.add(s3 + dur(c3) - 1 == 16)
    
    s_dub = If(c0 == 2, s0,
               If(c1 == 2, s1,
               If(c2 == 2, s2,
               If(c3 == 2, s3, 0))))
    s.add(s_dub <= 9)
    
    if s.check() == sat:
        m = s.model()
        c0_val = m[c0].as_long()
        c1_val = m[c1].as_long()
        c2_val = m[c2].as_long()
        c3_val = m[c3].as_long()
        order_vals = [c0_val, c1_val, c2_val, c3_val, 4]
        order_cities = [cities[i] for i in order_vals]
        
        dur_vals = [5, 4, 5, 5]
        s0_val = 1
        s1_val = s0_val + dur_vals[c0_val] - 1
        s2_val = s1_val + dur_vals[c1_val] - 1
        s3_val = s2_val + dur_vals[c2_val] - 1
        
        itinerary = []
        for d in range(1, 19):
            if d <= s1_val:
                itinerary.append({"day": d, "place": order_cities[0]})
            if s1_val <= d <= s2_val:
                itinerary.append({"day": d, "place": order_cities[1]})
            if s2_val <= d <= s3_val:
                itinerary.append({"day": d, "place": order_cities[2]})
            if s3_val <= d <= 16:
                itinerary.append({"day": d, "place": order_cities[3]})
            if 16 <= d <= 18:
                itinerary.append({"day": d, "place": order_cities[4]})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()