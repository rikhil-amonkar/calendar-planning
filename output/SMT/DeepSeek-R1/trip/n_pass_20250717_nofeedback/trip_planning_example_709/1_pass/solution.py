from z3 import *
import json

def main():
    # City mapping to integers
    cities = ["Helsinki", "Valencia", "Dubrovnik", "Porto", "Prague", "Reykjavik"]
    c_map = {name: idx for idx, name in enumerate(cities)}
    req_days = {
        c_map["Helsinki"]: 4,
        c_map["Valencia"]: 5,
        c_map["Dubrovnik"]: 4,
        c_map["Porto"]: 3,
        c_map["Prague"]: 3,
        c_map["Reykjavik"]: 4
    }
    
    # Define direct flight edges (both directions)
    edges = [
        (c_map["Helsinki"], c_map["Prague"]),
        (c_map["Prague"], c_map["Valencia"]),
        (c_map["Valencia"], c_map["Porto"]),
        (c_map["Helsinki"], c_map["Reykjavik"]),
        (c_map["Dubrovnik"], c_map["Helsinki"]),
        (c_map["Reykjavik"], c_map["Prague"])
    ]
    flight_set = set()
    for e in edges:
        flight_set.add(e)
        flight_set.add((e[1], e[0]))
    
    # Z3 variables
    s1, s2, s3, s4, s5, s6 = Ints('s1 s2 s3 s4 s5 s6')
    end1, end2, end3, end4, end5 = Ints('end1 end2 end3 end4 end5')
    
    constraints = []
    
    # End day constraints: 1 <= end1 <= end2 <= end3 <= end4 <= end5 <= 18
    constraints.append(And(end1 >= 1, end1 <= 18))
    constraints.append(And(end2 >= end1, end2 <= 18))
    constraints.append(And(end3 >= end2, end3 <= 18))
    constraints.append(And(end4 >= end3, end4 <= 18))
    constraints.append(And(end5 >= end4, end5 <= 18))
    
    # City assignment constraints: each s_i in [0,5]
    for s in [s1, s2, s3, s4, s5, s6]:
        constraints.append(And(s >= 0, s <= 5))
    
    # Segment lengths
    L1 = end1
    L2 = end2 - end1 + 1
    L3 = end3 - end2 + 1
    L4 = end4 - end3 + 1
    L5 = end5 - end4 + 1
    L6 = 19 - end5  # 18 - end5 + 1 = 19 - end5
    
    # Total days per city
    for city in range(6):
        total = Sum(
            [If(s1 == city, L1, 0),
             If(s2 == city, L2, 0),
             If(s3 == city, L3, 0),
             If(s4 == city, L4, 0),
             If(s5 == city, L5, 0),
             If(s6 == city, L6, 0)]
        )
        constraints.append(total == req_days[city])
    
    # Flight constraints between consecutive segments
    segments = [s1, s2, s3, s4, s5, s6]
    for i in range(5):
        s_i = segments[i]
        s_j = segments[i+1]
        conds = []
        for (a, b) in flight_set:
            conds.append(And(s_i == a, s_j == b))
        constraints.append(Or(conds))
    
    # Porto constraint: must be in Porto on at least one day between 16 and 18
    porto_days = []
    for d in [16, 17, 18]:
        cond = Or(
            And(d <= end1, s1 == c_map["Porto"]),
            And(end1 <= d, d <= end2, s2 == c_map["Porto"]),
            And(end2 <= d, d <= end3, s3 == c_map["Porto"]),
            And(end3 <= d, d <= end4, s4 == c_map["Porto"]),
            And(end4 <= d, d <= end5, s5 == c_map["Porto"]),
            And(end5 <= d, s6 == c_map["Porto"])
        )
        porto_days.append(cond)
    constraints.append(Or(porto_days))
    
    # Solve the constraints
    s = Solver()
    s.add(constraints)
    if s.check() == sat:
        m = s.model()
        # Extract values
        end1_val = m[end1].as_long()
        end2_val = m[end2].as_long()
        end3_val = m[end3].as_long()
        end4_val = m[end4].as_long()
        end5_val = m[end5].as_long()
        s_vals = [m[seg].as_long() for seg in segments]
        
        # Build itinerary
        itinerary = []
        for day in range(1, 19):
            if day <= end1_val:
                itinerary.append({"day": day, "place": cities[s_vals[0]]})
            if end1_val <= day <= end2_val:
                itinerary.append({"day": day, "place": cities[s_vals[1]]})
            if end2_val <= day <= end3_val:
                itinerary.append({"day": day, "place": cities[s_vals[2]]})
            if end3_val <= day <= end4_val:
                itinerary.append({"day": day, "place": cities[s_vals[3]]})
            if end4_val <= day <= end5_val:
                itinerary.append({"day": day, "place": cities[s_vals[4]]})
            if end5_val <= day:
                itinerary.append({"day": day, "place": cities[s_vals[5]]})
        
        # Output as JSON
        result = {'itinerary': itinerary}
        print(json.dumps(result))
    else:
        print(json.dumps({"error": "No solution found"}))

if __name__ == '__main__':
    main()