from z3 import *

def main():
    s = Solver()
    
    # Define the city indices and names
    cities = ["Reykjavik", "Stuttgart", "Stockholm", "Tallinn", "Oslo", "Split", "Geneva", "Porto"]
    city_to_index = {name: idx for idx, name in enumerate(cities)}
    index_to_city = {idx: name for idx, name in enumerate(cities)}
    
    # Durations for the middle segments (c1 to c6): 
    #   Stuttgart:1, Stockholm:2, Tallinn:3, Oslo:4, Split:5, Geneva:6
    dur_dict = {
        1: 5,   # Stuttgart
        2: 3,   # Stockholm
        3: 5,   # Tallinn
        4: 5,   # Oslo
        5: 3,   # Split
        6: 2    # Geneva
    }
    
    # Create Z3 variables for the 6 segments (c1 to c6)
    c1, c2, c3, c4, c5, c6 = Ints('c1 c2 c3 c4 c5 c6')
    s.add([c1 >= 1, c1 <= 6, c2 >= 1, c2 <= 6, c3 >= 1, c3 <= 6, c4 >= 1, c4 <= 6, c5 >= 1, c5 <= 6, c6 >= 1, c6 <= 6])
    s.add(Distinct([c1, c2, c3, c4, c5, c6]))
    
    # Define durations for each segment
    def dur(city_var):
        return If(city_var == 1, 5, 
                If(city_var == 2, 3,
                If(city_var == 3, 5,
                If(city_var == 4, 5,
                If(city_var == 5, 3,
                If(city_var == 6, 2, 0))))))
    
    d1 = dur(c1) + 1
    d2 = d1 + dur(c2) - 1
    d3 = d2 + dur(c3) - 1
    d4 = d3 + dur(c4) - 1
    d5 = d4 + dur(c5) - 1
    dur_c6 = dur(c6)
    s.add(dur_c6 == 20 - d5)
    
    s.add(d1 >= 2, d1 <= 19)
    s.add(d2 >= d1, d2 <= 19)
    s.add(d3 >= d2, d3 <= 19)
    s.add(d4 >= d3, d4 <= 19)
    s.add(d5 >= d4, d5 <= 19)
    s.add(dur_c6 >= 2, dur_c6 <= 5)  # dur_c6 must be one of 2,3,5
    
    # Stockholm constraint: if the segment is Stockholm (index 2) and it's in the first 4 segments, then its arrival day must be <=4
    s.add(If(c1 == 2, True, True))  # segment1 always arrives on day2 <=4
    s.add(If(c2 == 2, d1 <= 4, True))
    s.add(If(c3 == 2, d2 <= 4, True))
    s.add(If(c4 == 2, d3 <= 4, True))
    
    # Flight constraints: define allowed edges (both directions)
    allowed_edges = [
        (0,1), (0,2), (0,3), (0,4),
        (1,0), (1,2), (1,5), (1,7),
        (2,0), (2,1), (2,4), (2,5), (2,6),
        (3,0), (3,4),
        (4,0), (4,1), (4,2), (4,3), (4,5), (4,6), (4,7),
        (5,1), (5,2), (5,4), (5,6),
        (6,2), (6,4), (6,5), (6,7),
        (7,1), (7,4), (7,6)
    ]
    
    def edge(u, v):
        options = []
        for a, b in allowed_edges:
            options.append(And(u == a, v == b))
        return Or(options)
    
    # Flight constraints between consecutive segments
    s.add(edge(0, c1))          # Reykjavik (0) to c1
    s.add(edge(c1, c2))         # c1 to c2
    s.add(edge(c2, c3))         # c2 to c3
    s.add(edge(c3, c4))         # c3 to c4
    s.add(edge(c4, c5))         # c4 to c5
    s.add(edge(c5, c6))         # c5 to c6
    s.add(edge(c6, 7))          # c6 to Porto (7)
    
    if s.check() == sat:
        m = s.model()
        c1_val = m[c1].as_long()
        c2_val = m[c2].as_long()
        c3_val = m[c3].as_long()
        c4_val = m[c4].as_long()
        c5_val = m[c5].as_long()
        c6_val = m[c6].as_long()
        
        # Compute d1 to d5 from the model
        dur1 = dur_dict[c1_val]
        d1_val = dur1 + 1
        dur2 = dur_dict[c2_val]
        d2_val = d1_val + dur2 - 1
        dur3 = dur_dict[c3_val]
        d3_val = d2_val + dur3 - 1
        dur4 = dur_dict[c4_val]
        d4_val = d3_val + dur4 - 1
        dur5 = dur_dict[c5_val]
        d5_val = d4_val + dur5 - 1
        dur6 = dur_dict[c6_val]
        # Check: dur6 should equal 20 - d5_val
        assert dur6 == 20 - d5_val, "Inconsistency in duration for c6"
        
        # Build the segments: [Reykjavik, c1, c2, c3, c4, c5, c6, Porto]
        segments = [0, c1_val, c2_val, c3_val, c4_val, c5_val, c6_val, 7]
        # Arrival days for each segment: 
        #   Reykjavik:1, c1:2, c2:d1, c3:d2, c4:d3, c5:d4, c6:d5, Porto:19
        arr_days = [1, 2, d1_val, d2_val, d3_val, d4_val, d5_val, 19]
        # Departure days for each segment (for non-last segments, this is the day of flight, which is the same as the next segment's arrival)
        # For the last segment (Porto), we stay until day21, so dep=21 (but we don't use it for flight)
        dep_days = [2, d1_val, d2_val, d3_val, d4_val, d5_val, 19, 21]
        
        itinerary = []
        for i in range(8):
            city_idx = segments[i]
            city_name = index_to_city[city_idx]
            arr = arr_days[i]
            dep = dep_days[i]
            
            # Entire stay record: for non-last segments, the entire stay is from arr to dep (inclusive)
            # For the last segment (Porto), the entire stay is from arr (19) to 21.
            if i < 7:
                day_range_str = f"Day {arr}-{dep}"
            else:
                day_range_str = f"Day {arr}-21"
            itinerary.append({"day_range": day_range_str, "place": city_name})
            
            # If not the last segment, add flight records: departure from current city and arrival in next city on the same day (dep)
            if i < 7:
                # Flight day: departure from current city
                itinerary.append({"day_range": f"Day {dep}", "place": city_name})
                next_city_idx = segments[i+1]
                next_city_name = index_to_city[next_city_idx]
                itinerary.append({"day_range": f"Day {dep}", "place": next_city_name})
        
        # Output the itinerary as a JSON dictionary
        result = {"itinerary": itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()