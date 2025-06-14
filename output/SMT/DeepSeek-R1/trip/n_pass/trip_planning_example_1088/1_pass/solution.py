from z3 import *

def main():
    cities = ["Reykjavik", "Stuttgart", "Stockholm", "Tallinn", "Oslo", "Split", "Geneva", "Porto"]
    dur_all = [2, 5, 3, 5, 5, 3, 2, 3]  # durations for cities 0 to 7

    edge_set = set()
    edges = [
        (0, 1), (0, 2), (0, 3), (0, 4),
        (1, 2), (1, 5), (1, 7),
        (2, 4), (2, 5), (2, 6),
        (3, 4),
        (4, 5), (4, 6), (4, 7),
        (5, 6),
        (6, 7)
    ]
    for u, v in edges:
        edge_set.add((min(u, v), max(u, v)))
    
    s = Solver()
    
    seg_city = [Int(f'seg_city_{i}') for i in range(6)]
    e = [Int(f'e{i+1}') for i in range(6)]  # e1, e2, ..., e6

    # Constraint: seg_city contains distinct integers from 1 to 6
    s.add(Distinct(seg_city))
    for i in range(6):
        s.add(seg_city[i] >= 1, seg_city[i] <= 6)
    
    # Duration constraints
    s.add(e[0] - 1 == dur_all[seg_city[0]])
    s.add(e[1] - e[0] + 1 == dur_all[seg_city[1]])
    s.add(e[2] - e[1] + 1 == dur_all[seg_city[2]])
    s.add(e[3] - e[2] + 1 == dur_all[seg_city[3]])
    s.add(e[4] - e[3] + 1 == dur_all[seg_city[4]])
    s.add(e[5] == 19)  # because segment6 ends at day 19
    s.add(20 - e[4] == dur_all[seg_city[5]])  # segment6: start e5, end 19 -> length = 19 - e5 + 1 = 20 - e5

    # Stockholm constraint: if a segment (index j in 1 to 5) is Stockholm (city2), then its start day <= 4
    for j in range(1, 6):
        s.add(If(seg_city[j] == 2, e[j-1] <= 4, True))
    
    # Flight constraints for 7 legs
    legs = [
        (0, seg_city[0]),
        (seg_city[0], seg_city[1]),
        (seg_city[1], seg_city[2]),
        (seg_city[2], seg_city[3]),
        (seg_city[3], seg_city[4]),
        (seg_city[4], seg_city[5]),
        (seg_city[5], 7)
    ]
    for (a, b) in legs:
        low = If(a < b, a, b)
        high = If(a < b, b, a)
        cond = False
        for edge in edge_set:
            x, y = edge
            cond = Or(cond, And(low == x, high == y))
        s.add(cond)
    
    if s.check() == sat:
        m = s.model()
        seg_city_val = [m[var].as_long() for var in seg_city]
        e_val = [m[var].as_long() for var in e]
        
        print("Full itinerary:")
        print("City\tStart\tEnd")
        print("Reykjavik\t1\t2")
        start_days = [2] + e_val[:-1]
        for i in range(6):
            city_idx = seg_city_val[i]
            city_name = cities[city_idx]
            start = start_days[i]
            end = e_val[i]
            print(f"{city_name}\t{start}\t{end}")
        print("Porto\t19\t21")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()