from z3 import *
import json

def main():
    # City indices
    PRG, TLL, WAW, POR, NAP, MIL, LIS, SAN, RIX, STO = 0,1,2,3,4,5,6,7,8,9
    city_names = {
        PRG: "Prague",
        TLL: "Tallinn",
        WAW: "Warsaw",
        POR: "Porto",
        NAP: "Naples",
        MIL: "Milan",
        LIS: "Lisbon",
        SAN: "Santorini",
        RIX: "Riga",
        STO: "Stockholm"
    }
    req_days = [5, 3, 2, 3, 5, 3, 5, 5, 4, 2]
    
    # Create a Z3 array for required days
    req_days_array = Array('req_days', IntSort(), IntSort())
    for i, days in enumerate(req_days):
        req_days_array = Store(req_days_array, i, days)
    
    direct_flights = [
        (RIX, PRG), (STO, MIL), (RIX, MIL), (LIS, STO), (STO, SAN),
        (NAP, WAW), (LIS, WAW), (NAP, MIL), (LIS, NAP), (RIX, TLL),
        (TLL, PRG), (STO, WAW), (RIX, WAW), (LIS, RIX), (RIX, STO),
        (LIS, POR), (LIS, PRG), (MIL, POR), (PRG, MIL), (LIS, MIL),
        (WAW, POR), (WAW, TLL), (SAN, MIL), (STO, PRG), (STO, TLL),
        (WAW, MIL), (SAN, NAP), (WAW, PRG)
    ]
    
    allowed_pairs = set()
    for (a, b) in direct_flights:
        allowed_pairs.add((a, b))
        allowed_pairs.add((b, a))
    
    s = Solver()
    order = [Int(f'order_{i}') for i in range(10)]
    for i in range(10):
        s.add(order[i] >= 0, order[i] <= 9)
    s.add(Distinct(order))
    
    S = [Int(f'S_{i}') for i in range(10)]
    s.add(S[0] == 1)
    for i in range(1, 10):
        s.add(S[i] == S[i-1] + Select(req_days_array, order[i-1]) - 1)
    
    for i in range(9):
        city_i = order[i]
        city_j = order[i+1]
        s.add(Or([And(city_i == a, city_j == b) for (a, b) in allowed_pairs]))
    
    s.add(Or([And(order[i] == RIX, S[i] == 5) for i in range(10)]))
    s.add(Or([And(order[i] == TLL, S[i] == 18) for i in range(10)]))
    s.add(Or([And(order[i] == MIL, S[i] == 24) for i in range(10)]))
    
    if s.check() == sat:
        m = s.model()
        order_val = [m.evaluate(order[i]).as_long() for i in range(10)]
        S_val = [m.evaluate(S[i]).as_long() for i in range(10)]
        itinerary = []
        for i in range(10):
            city_index = order_val[i]
            start_day = S_val[i]
            end_day = start_day + req_days[city_index] - 1
            itinerary.append({
                "day_range": f"Day {start_day}-{end_day}",
                "place": city_names[city_index]
            })
        print(json.dumps({"itinerary": itinerary}))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()