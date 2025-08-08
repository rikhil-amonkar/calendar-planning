from z3 import *
import json

def main():
    # City mapping: integers to names
    city_map = {
        0: "Prague",
        1: "Stuttgart",
        2: "Split",
        3: "Krakow",
        4: "Florence"
    }
    
    # Required days per city index
    req_days = [4, 2, 2, 2, 2]
    
    # Direct flights (undirected)
    flights = [(1, 2), (0, 4), (3, 1), (3, 2), (2, 0), (3, 0)]
    allowed_pairs = set()
    for a, b in flights:
        allowed_pairs.add((a, b))
        allowed_pairs.add((b, a))
    
    # Position variables for each city (segment index)
    pos_P = Int('pos_P')  # Prague
    pos_S = Int('pos_S')  # Stuttgart
    pos_Sp = Int('pos_Sp')  # Split
    pos_K = Int('pos_K')  # Krakow
    pos_F = Int('pos_F')  # Florence
    
    # Day variables for segment transitions
    d0 = Int('d0')
    d1 = Int('d1')
    d2 = Int('d2')
    d3 = Int('d3')
    
    # City at each segment
    city_at = [Int(f'city_at_{i}') for i in range(5)]
    
    s = Solver()
    
    # Each position is between 0 and 4
    s.add(pos_P >= 0, pos_P < 5)
    s.add(pos_S >= 0, pos_S < 5)
    s.add(pos_Sp >= 0, pos_Sp < 5)
    s.add(pos_K >= 0, pos_K < 5)
    s.add(pos_F >= 0, pos_F < 5)
    
    # All positions are distinct
    s.add(Distinct(pos_P, pos_S, pos_Sp, pos_K, pos_F))
    
    # Define city_at for each segment using temporary expr variable
    for i in range(5):
        expr = If(pos_P == i, 0,
                If(pos_S == i, 1,
                If(pos_Sp == i, 2,
                If(pos_K == i, 3,
                If(pos_F == i, 4, -1)))))
        s.add(city_at[i] == expr)
        # Ensure city_at[i] is valid
        s.add(Or([city_at[i] == j for j in range(5)]))
    
    # Required days per segment
    req0 = Int('req0')
    req1 = Int('req1')
    req2 = Int('req2')
    req3 = Int('req3')
    req4 = Int('req4')
    for i, req in enumerate([req0, req1, req2, req3, req4]):
        s.add(req == req_days[city_at[i]])
    
    # Constraints for segment days
    s.add(d0 == req0)
    s.add(d1 == d0 + req1 - 1)
    s.add(d2 == d1 + req2 - 1)
    s.add(d3 == d2 + req3 - 1)
    s.add(d3 == 7)  # Total days must be 8, so segment4 ends at day 8 (segment4: d3 to 8 -> 2 days)
    
    # Flight constraints between consecutive segments
    for i in range(4):
        city_i = city_at[i]
        city_j = city_at[i+1]
        s.add(Or([And(city_i == a, city_j == b) for (a, b) in allowed_pairs]))
    
    # Define start and end days for each segment
    starts = [1, d0, d1, d2, d3]
    ends = [d0, d1, d2, d3, 8]
    
    # Helper function to get start/end day for a city by its segment index
    def get_day_for_city(pos, day_list):
        return If(pos == 0, day_list[0],
                If(pos == 1, day_list[1],
                If(pos == 2, day_list[2],
                If(pos == 3, day_list[3],
                If(pos == 4, day_list[4], 0)))))
    
    # Constraints for Stuttgart: must include days 2 and 3
    start_stuttgart = get_day_for_city(pos_S, starts)
    end_stuttgart = get_day_for_city(pos_S, ends)
    s.add(start_stuttgart <= 2)
    s.add(end_stuttgart >= 3)
    
    # Constraints for Split: must include days 3 and 4
    start_split = get_day_for_city(pos_Sp, starts)
    end_split = get_day_for_city(pos_Sp, ends)
    s.add(start_split <= 3)
    s.add(end_split >= 4)
    
    # Solve the problem
    if s.check() == sat:
        m = s.model()
        # Get the segment days
        d0_val = m[d0].as_long()
        d1_val = m[d1].as_long()
        d2_val = m[d2].as_long()
        d3_val = m[d3].as_long()
        starts_val = [1, d0_val, d1_val, d2_val, d3_val]
        ends_val = [d0_val, d1_val, d2_val, d3_val, 8]
        
        # Get the city for each segment
        city_at_val = []
        for i in range(5):
            city_at_val.append(m[city_at[i]].as_long())
        
        # Build itinerary
        itinerary = []
        for day in range(1, 9):
            for seg in range(5):
                start_seg = starts_val[seg]
                end_seg = ends_val[seg]
                if start_seg <= day <= end_seg:
                    city_name = city_map[city_at_val[seg]]
                    itinerary.append({"day": day, "place": city_name})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print(json.dumps({"error": "No solution found"}))

if __name__ == "__main__":
    main()