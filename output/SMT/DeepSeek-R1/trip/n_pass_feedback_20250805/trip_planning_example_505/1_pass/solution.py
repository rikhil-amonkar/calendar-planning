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
    
    # Direct flights (undirected)
    flights = [(1, 2), (0, 4), (3, 1), (3, 2), (2, 0), (3, 0)]
    allowed_pairs = set()
    for a, b in flights:
        allowed_pairs.add((a, b))
        allowed_pairs.add((b, a))
    allowed_pairs_list = list(allowed_pairs)
    
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
    
    # Required days for each segment
    req0 = If(pos_P == 0, 4, 2)
    req1 = If(pos_P == 1, 4, 2)
    req2 = If(pos_P == 2, 4, 2)
    req3 = If(pos_P == 3, 4, 2)
    req4 = If(pos_P == 4, 4, 2)
    
    # Last segment must be 2 days (d3 = 7)
    s.add(req4 == 2)
    s.add(d0 == req0)
    s.add(d1 == d0 + req1 - 1)
    s.add(d2 == d1 + req2 - 1)
    s.add(d3 == d2 + req3 - 1)
    s.add(d3 == 7)
    
    # Define city_at for each segment
    for i in range(5):
        s.add(city_at[i] == If(pos_P == i, 0,
                               If(pos_S == i, 1,
                                 If(pos_Sp == i, 2,
                                   If(pos_K == i, 3,
                                     If(pos_F == i, 4, -1)))))
    
    # Flight constraints between consecutive segments
    for i in range(4):
        conds = []
        for a, b in allowed_pairs_list:
            conds.append(And(city_at[i] == a, city_at[i+1] == b))
        s.add(Or(conds))
    
    # Constraints for Stuttgart: must include days 2 and 3
    arr_S = If(pos_S == 0, 1,
               If(pos_S == 1, d0,
                 If(pos_S == 2, d1,
                   If(pos_S == 3, d2,
                     If(pos_S == 4, d3, -1)))))
    dep_S = If(pos_S == 0, d0,
               If(pos_S == 1, d1,
                 If(pos_S == 2, d2,
                   If(pos_S == 3, d3,
                     If(pos_S == 4, 8, -1)))))
    s.add(arr_S <= 2)
    s.add(dep_S >= 3)
    
    # Constraints for Split: must include days 3 and 4
    arr_Sp = If(pos_Sp == 0, 1,
                If(pos_Sp == 1, d0,
                  If(pos_Sp == 2, d1,
                    If(pos_Sp == 3, d2,
                      If(pos_Sp == 4, d3, -1)))))
    dep_Sp = If(pos_Sp == 0, d0,
                If(pos_Sp == 1, d1,
                  If(pos_Sp == 2, d2,
                    If(pos_Sp == 3, d3,
                      If(pos_Sp == 4, 8, -1)))))
    s.add(arr_Sp <= 3)
    s.add(dep_Sp >= 4)
    
    # Solve the problem
    if s.check() == sat:
        m = s.model()
        d0_val = m[d0].as_long()
        d1_val = m[d1].as_long()
        d2_val = m[d2].as_long()
        d3_val = m[d3].as_long()
        
        city_at_val = []
        for i in range(5):
            city_at_val.append(m[city_at[i]].as_long())
        
        # Build itinerary
        itinerary = []
        for day in range(1, 9):
            if day <= d0_val:
                itinerary.append({"day": day, "place": city_map[city_at_val[0]]})
            if day >= d0_val and day <= d1_val:
                itinerary.append({"day": day, "place": city_map[city_at_val[1]]})
            if day >= d1_val and day <= d2_val:
                itinerary.append({"day": day, "place": city_map[city_at_val[2]]})
            if day >= d2_val and day <= d3_val:
                itinerary.append({"day": day, "place": city_map[city_at_val[3]]})
            if day >= d3_val and day <= 8:
                itinerary.append({"day": day, "place": city_map[city_at_val[4]]})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print(json.dumps({"error": "No solution found"}))

if __name__ == "__main__":
    main()