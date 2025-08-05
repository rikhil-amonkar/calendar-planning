import json
from z3 import *

def main():
    manchester = 0
    istanbul = 1
    venice = 2
    krakow = 3
    lyon = 4
    cities = ["Manchester", "Istanbul", "Venice", "Krakow", "Lyon"]
    required_days = [3, 7, 7, 6, 2]
    
    edge_set = set()
    edges = [(0,1), (0,2), (0,3), (1,2), (1,3), (1,4), (2,4)]
    for (a, b) in edges:
        edge_set.add((min(a, b), max(a, b)))
    
    flights = []
    for (a, b) in edge_set:
        flights.append((a, b))
        flights.append((b, a))
    
    s = Solver()
    s1 = Int('s1')
    e = [Int('e_%d' % i) for i in range(21)]
    
    s.add(s1 >= 0, s1 <= 4)
    for i in range(21):
        s.add(e[i] >= 0, e[i] <= 4)
    
    # Flight constraint for day1
    options_day1 = []
    for (a, b) in flights:
        options_day1.append(And(s1 == a, e[0] == b))
    s.add(If(s1 != e[0], Or(options_day1), True))
    
    # Flight constraints for days 2 to 21
    for i in range(20):
        options = []
        for (a, b) in flights:
            options.append(And(e[i] == a, e[i+1] == b))
        s.add(If(e[i] != e[i+1], Or(options), True))
    
    # Total days per city
    for c in range(5):
        conds = []
        conds.append(Or(s1 == c, e[0] == c))
        for i in range(20):
            conds.append(Or(e[i] == c, e[i+1] == c))
        total = 0
        for cond in conds:
            total += If(cond, 1, 0)
        s.add(total == required_days[c])
    
    # Event constraints
    # Manchester: at least one of days 1,2,3
    cond_manchester = []
    cond_manchester.append(Or(s1 == manchester, e[0] == manchester))
    cond_manchester.append(Or(e[0] == manchester, e[1] == manchester))
    cond_manchester.append(Or(e[1] == manchester, e[2] == manchester))
    s.add(Or(cond_manchester))
    
    # Venice: at least one of days 3 to 9
    cond_venice = []
    for i in range(2, 9):
        cond_venice.append(Or(e[i-1] == venice, e[i] == venice))
    s.add(Or(cond_venice))
    
    # Flight days must be 4
    flight_days = If(s1 != e[0], 1, 0)
    for i in range(20):
        flight_days += If(e[i] != e[i+1], 1, 0)
    s.add(flight_days == 4)
    
    if s.check() == sat:
        m = s.model()
        s1_val = m[s1].as_long()
        e_vals = [m[e_i].as_long() for e_i in e]
        itinerary_list = []
        for i in range(21):
            day = i + 1
            city_name = cities[e_vals[i]]
            itinerary_list.append({"day": day, "place": city_name})
        result = {"itinerary": itinerary_list}
        print(json.dumps(result))
    else:
        print("No solution")

if __name__ == "__main__":
    main()