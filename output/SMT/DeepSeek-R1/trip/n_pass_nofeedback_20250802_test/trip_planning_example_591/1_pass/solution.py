from z3 import *
import json

def main():
    # Define the variables for the positions
    p0, p1, p2, p3, p4 = Ints('p0 p1 p2 p3 p4')
    s = Solver()
    
    # Each position must be between 0 and 4 (cities: 0=Geneva, 1=Munich, 2=Valencia, 3=Bucharest, 4=Stuttgart)
    s.add(p0 >= 0, p0 <= 4)
    s.add(p1 >= 0, p1 <= 4)
    s.add(p2 >= 0, p2 <= 4)
    s.add(p3 >= 0, p3 <= 4)
    s.add(p4 >= 0, p4 <= 4)
    s.add(Distinct(p0, p1, p2, p3, p4))
    
    # Durations for each city: Geneva=4, Munich=7, Valencia=6, Bucharest=2, Stuttgart=2
    d0 = If(p0 == 0, 4, If(p0 == 1, 7, If(p0 == 2, 6, If(p0 == 3, 2, 2))))
    d1 = If(p1 == 0, 4, If(p1 == 1, 7, If(p1 == 2, 6, If(p1 == 3, 2, 2))))
    d2 = If(p2 == 0, 4, If(p2 == 1, 7, If(p2 == 2, 6, If(p2 == 3, 2, 2))))
    d3 = If(p3 == 0, 4, If(p3 == 1, 7, If(p3 == 2, 6, If(p3 == 3, 2, 2))))
    d4 = If(p4 == 0, 4, If(p4 == 1, 7, If(p4 == 2, 6, If(p4 == 3, 2, 2))))
    
    # Start days for each segment
    s0 = 1
    s1 = d0
    s2 = d0 + d1 - 1
    s3 = d0 + d1 + d2 - 2
    s4 = d0 + d1 + d2 + d3 - 3
    
    # Constraints for Geneva: the start day of Geneva must be <= 4
    s.add(Implies(p0 == 0, s0 <= 4))
    s.add(Implies(p1 == 0, s1 <= 4))
    s.add(Implies(p2 == 0, s2 <= 4))
    s.add(Implies(p3 == 0, s3 <= 4))
    s.add(Implies(p4 == 0, s4 <= 4))
    
    # Constraints for Munich: the start day of Munich must be <= 10
    s.add(Implies(p0 == 1, s0 <= 10))
    s.add(Implies(p1 == 1, s1 <= 10))
    s.add(Implies(p2 == 1, s2 <= 10))
    s.add(Implies(p3 == 1, s3 <= 10))
    s.add(Implies(p4 == 1, s4 <= 10))
    
    # Allowed edges (undirected): 
    allowed_edges = [
        (0,1), (1,0),
        (0,2), (2,0),
        (1,2), (2,1),
        (1,3), (3,1),
        (2,3), (3,2),
        (2,4), (4,2)
    ]
    
    # Constraints for consecutive positions: (p0,p1), (p1,p2), (p2,p3), (p3,p4) must be in allowed_edges
    edge01 = Or([And(p0 == x, p1 == y) for (x,y) in allowed_edges])
    edge12 = Or([And(p1 == x, p2 == y) for (x,y) in allowed_edges])
    edge23 = Or([And(p2 == x, p3 == y) for (x,y) in allowed_edges])
    edge34 = Or([And(p3 == x, p4 == y) for (x,y) in allowed_edges])
    s.add(edge01, edge12, edge23, edge34)
    
    # Total duration must be 21
    s.add(d0 + d1 + d2 + d3 + d4 == 21)
    
    if s.check() == sat:
        m = s.model()
        vp0 = m[p0].as_long()
        vp1 = m[p1].as_long()
        vp2 = m[p2].as_long()
        vp3 = m[p3].as_long()
        vp4 = m[p4].as_long()
        
        dur = [4, 7, 6, 2, 2]
        d0_val = dur[vp0]
        d1_val = dur[vp1]
        d2_val = dur[vp2]
        d3_val = dur[vp3]
        d4_val = dur[vp4]
        
        s0_val = 1
        s1_val = d0_val
        s2_val = d0_val + d1_val - 1
        s3_val = d0_val + d1_val + d2_val - 2
        s4_val = d0_val + d1_val + d2_val + d3_val - 3
        
        segments = [
            (vp0, s0_val, s0_val + d0_val - 1),
            (vp1, s1_val, s1_val + d1_val - 1),
            (vp2, s2_val, s2_val + d2_val - 1),
            (vp3, s3_val, s3_val + d3_val - 1),
            (vp4, s4_val, s4_val + d4_val - 1)
        ]
        
        city_names = {
            0: "Geneva",
            1: "Munich",
            2: "Valencia",
            3: "Bucharest",
            4: "Stuttgart"
        }
        
        itinerary_list = []
        for seg in segments:
            city_idx, start, end = seg
            city = city_names[city_idx]
            for day in range(start, end + 1):
                itinerary_list.append({"day": day, "place": city})
                
        result = {"itinerary": itinerary_list}
        print(json.dumps(result))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()