from z3 import *

def main():
    city_names = ["Manchester", "Istanbul", "Venice", "Krakow", "Lyon"]
    days_arr = [3, 7, 7, 6, 2]
    allowed_edges = [(0,1), (0,2), (0,3), (1,2), (1,3), (1,4), (2,4)]
    
    c0, c1, c2, c3, c4 = Ints('c0 c1 c2 c3 c4')
    c = [c0, c1, c2, c3, c4]
    
    s = Solver()
    
    for ci in c:
        s.add(ci >= 0, ci <= 4)
    s.add(Distinct(c))
    
    def day_val(ci):
        return If(ci == 0, days_arr[0],
               If(ci == 1, days_arr[1],
               If(ci == 2, days_arr[2],
               If(ci == 3, days_arr[3], days_arr[4]))))
    
    s0 = 1
    s1 = s0 + day_val(c0) - 1
    s2 = s1 + day_val(c1) - 1
    s3 = s2 + day_val(c2) - 1
    s4 = s3 + day_val(c3) - 1
    s_start = [s0, s1, s2, s3, s4]
    
    man_index = 0
    venice_index = 2
    
    for i in range(5):
        s.add(If(c[i] == man_index, s_start[i] <= 3, True))
        s.add(If(c[i] == venice_index, s_start[i] <= 9, True))
    
    for i in range(4):
        cond = Or([Or(And(c[i] == a, c[i+1] == b), And(c[i] == b, c[i+1] == a)) for (a, b) in allowed_edges])
        s.add(cond)
    
    if s.check() == sat:
        m = s.model()
        c_val = [m[ci].as_long() for ci in c]
        d_val = [days_arr[idx] for idx in c_val]
        
        s0_val = 1
        s1_val = s0_val + d_val[0] - 1
        s2_val = s1_val + d_val[1] - 1
        s3_val = s2_val + d_val[2] - 1
        s4_val = s3_val + d_val[3] - 1
        s_vals = [s0_val, s1_val, s2_val, s3_val, s4_val]
        
        itinerary = []
        
        # Segment0
        city0 = city_names[c_val[0]]
        itinerary.append({"day_range": f"Day {s0_val}-{s1_val}", "place": city0})
        itinerary.append({"day_range": f"Day {s1_val}", "place": city0})
        
        # Segment1
        city1 = city_names[c_val[1]]
        itinerary.append({"day_range": f"Day {s1_val}", "place": city1})
        itinerary.append({"day_range": f"Day {s1_val}-{s2_val}", "place": city1})
        itinerary.append({"day_range": f"Day {s2_val}", "place": city1})
        
        # Segment2
        city2 = city_names[c_val[2]]
        itinerary.append({"day_range": f"Day {s2_val}", "place": city2})
        itinerary.append({"day_range": f"Day {s2_val}-{s3_val}", "place": city2})
        itinerary.append({"day_range": f"Day {s3_val}", "place": city2})
        
        # Segment3
        city3 = city_names[c_val[3]]
        itinerary.append({"day_range": f"Day {s3_val}", "place": city3})
        itinerary.append({"day_range": f"Day {s3_val}-{s4_val}", "place": city3})
        itinerary.append({"day_range": f"Day {s4_val}", "place": city3})
        
        # Segment4
        city4 = city_names[c_val[4]]
        itinerary.append({"day_range": f"Day {s4_val}", "place": city4})
        itinerary.append({"day_range": f"Day {s4_val}-21", "place": city4})
        
        result = {"itinerary": itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()