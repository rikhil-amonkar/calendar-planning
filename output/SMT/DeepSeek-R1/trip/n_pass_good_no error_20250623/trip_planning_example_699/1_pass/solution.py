from z3 import *
import json

def main():
    # Define the direct flights as tuples of city indices
    direct_flights_int = [
        (1, 4),  # Dublin and London
        (0, 1),  # Hamburg and Dublin
        (2, 3),  # Helsinki and Reykjavik
        (0, 4),  # Hamburg and London
        (1, 2),  # Dublin and Helsinki
        (3, 4),  # Reykjavik and London
        (4, 5),  # London and Mykonos
        (1, 3),  # Dublin and Reykjavik
        (0, 2),  # Hamburg and Helsinki
        (2, 4)   # Helsinki and London
    ]
    
    # Define segment variables for segments 2,3,4,5 (segments 0 and 1 are fixed)
    seg2 = Int('seg2')
    seg3 = Int('seg3')
    seg4 = Int('seg4')
    seg5 = Int('seg5')
    seg_cities = [seg2, seg3, seg4, seg5]
    
    s = Solver()
    
    # Each segment city must be one of 2,3,4,5 (Helsinki, Reykjavik, London, Mykonos)
    for sc in seg_cities:
        s.add(sc >= 2, sc <= 5)
    
    # All segment cities must be distinct
    s.add(Distinct(seg_cities))
    
    # Fixed segments: Hamburg (0) and Dublin (1)
    start0 = 1
    end0 = 2
    start1 = 2
    end1 = 6
    
    # Segment2 starts at day 6
    start2 = 6
    # Compute the end day for segment2 based on the city's required days
    req2 = If(seg2 == 2, 4, If(seg2 == 3, 2, If(seg2 == 4, 5, 3)))
    end2 = start2 + req2 - 1
    
    # Segment3 starts at the end of segment2
    start3 = end2
    req3 = If(seg3 == 2, 4, If(seg3 == 3, 2, If(seg3 == 4, 5, 3)))
    end3 = start3 + req3 - 1
    
    # Segment4 starts at the end of segment3
    start4 = end3
    req4 = If(seg4 == 2, 4, If(seg4 == 3, 2, If(seg4 == 4, 5, 3)))
    end4 = start4 + req4 - 1
    
    # Segment5 starts at the end of segment4
    start5 = end4
    req5 = If(seg5 == 2, 4, If(seg5 == 3, 2, If(seg5 == 4, 5, 3)))
    end5 = start5 + req5 - 1
    
    # The entire trip must end by day 16
    s.add(end5 <= 16)
    
    # Reykjavik (city index 3) must be visited from day 9 to day 10
    s.add(Or(
        And(seg2 == 3, start2 == 9),
        And(seg3 == 3, start3 == 9),
        And(seg4 == 3, start4 == 9),
        And(seg5 == 3, start5 == 9)
    ))
    
    # Flight constraints between consecutive segments
    # Flight from segment1 (Dublin,1) to segment2 (seg2)
    flight1_ok = False
    for (c1, c2) in direct_flights_int:
        flight1_ok = Or(flight1_ok, Or(And(1 == c1, seg2 == c2), And(1 == c2, seg2 == c1)))
    s.add(flight1_ok)
    
    # Flight from segment2 (seg2) to segment3 (seg3)
    flight2_ok = False
    for (c1, c2) in direct_flights_int:
        flight2_ok = Or(flight2_ok, Or(And(seg2 == c1, seg3 == c2), And(seg2 == c2, seg3 == c1)))
    s.add(flight2_ok)
    
    # Flight from segment3 (seg3) to segment4 (seg4)
    flight3_ok = False
    for (c1, c2) in direct_flights_int:
        flight3_ok = Or(flight3_ok, Or(And(seg3 == c1, seg4 == c2), And(seg3 == c2, seg4 == c1)))
    s.add(flight3_ok)
    
    # Flight from segment4 (seg4) to segment5 (seg5)
    flight4_ok = False
    for (c1, c2) in direct_flights_int:
        flight4_ok = Or(flight4_ok, Or(And(seg4 == c1, seg5 == c2), And(seg4 == c2, seg5 == c1)))
    s.add(flight4_ok)
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        # Get the values for the segment cities
        v_seg2 = m[seg2].as_long()
        v_seg3 = m[seg3].as_long()
        v_seg4 = m[seg4].as_long()
        v_seg5 = m[seg5].as_long()
        
        # Map city indices to names
        city_map = {
            0: "Hamburg",
            1: "Dublin",
            2: "Helsinki",
            3: "Reykjavik",
            4: "London",
            5: "Mykonos"
        }
        
        # The segments: 0,1,2,3,4,5
        seg_city_vals = [0, 1, v_seg2, v_seg3, v_seg4, v_seg5]
        
        # Start and end days for each segment
        starts = [1, 2, 6, None, None, None]
        ends = [2, 6, None, None, None, None]
        
        # Compute starts and ends for segments 2,3,4,5
        # Segment2
        if v_seg2 == 2:
            req2_val = 4
        elif v_seg2 == 3:
            req2_val = 2
        elif v_seg2 == 4:
            req2_val = 5
        else:  # v_seg2 == 5
            req2_val = 3
        end2_val = 6 + req2_val - 1
        ends[2] = end2_val
        starts[3] = end2_val
        
        # Segment3
        if v_seg3 == 2:
            req3_val = 4
        elif v_seg3 == 3:
            req3_val = 2
        elif v_seg3 == 4:
            req3_val = 5
        else:  # v_seg3 == 5
            req3_val = 3
        end3_val = starts[3] + req3_val - 1
        ends[3] = end3_val
        starts[4] = end3_val
        
        # Segment4
        if v_seg4 == 2:
            req4_val = 4
        elif v_seg4 == 3:
            req4_val = 2
        elif v_seg4 == 4:
            req4_val = 5
        else:  # v_seg4 == 5
            req4_val = 3
        end4_val = starts[4] + req4_val - 1
        ends[4] = end4_val
        starts[5] = end4_val
        
        # Segment5
        if v_seg5 == 2:
            req5_val = 4
        elif v_seg5 == 3:
            req5_val = 2
        elif v_seg5 == 4:
            req5_val = 5
        else:  # v_seg5 == 5
            req5_val = 3
        end5_val = starts[5] + req5_val - 1
        ends[5] = end5_val
        
        # Build the itinerary
        itinerary = []
        for i in range(0, 6):
            city_name = city_map[seg_city_vals[i]]
            start_day = starts[i]
            end_day = ends[i]
            # Continuous stay record
            if start_day == end_day:
                day_range_str = f"Day {start_day}"
            else:
                day_range_str = f"Day {start_day}-{end_day}"
            itinerary.append({"day_range": day_range_str, "place": city_name})
            
            # If not the last segment, add departure and arrival for the flight day
            if i < 5:
                # Departure from current city on end_day
                itinerary.append({"day_range": f"Day {end_day}", "place": city_name})
                # Arrival in next city on end_day
                next_city = city_map[seg_city_vals[i+1]]
                itinerary.append({"day_range": f"Day {end_day}", "place": next_city})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        # No solution found
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()