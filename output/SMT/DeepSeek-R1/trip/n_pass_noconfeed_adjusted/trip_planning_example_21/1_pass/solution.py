from z3 import *
import json

def main():
    # Cities: Mykonos (0), Vienna (1), Venice (2)
    s = [Int('s_%i' % i) for i in range(11)]
    solver = Solver()
    
    # Each s[i] must be 0, 1, or 2
    for i in range(11):
        solver.add(s[i] >= 0, s[i] <= 2)
    
    # Direct flights: Mykonos<->Vienna, Vienna<->Venice
    for i in range(10):
        solver.add(If(s[i] != s[i+1],
                     Or(And(s[i] == 0, s[i+1] == 1),
                        And(s[i] == 1, s[i+1] == 0),
                        And(s[i] == 1, s[i+1] == 2),
                        And(s[i] == 2, s[i+1] == 1)),
                     True))
    
    # Total days in each city
    venice_count = Sum([If(Or(s[i] == 2, s[i+1] == 2), 1, 0) for i in range(10)])
    mykonos_count = Sum([If(Or(s[i] == 0, s[i+1] == 0), 1, 0) for i in range(10)])
    vienna_count = Sum([If(Or(s[i] == 1, s[i+1] == 1), 1, 0) for i in range(10)])
    
    solver.add(venice_count == 6)
    solver.add(mykonos_count == 2)
    solver.add(vienna_count == 4)
    
    if solver.check() == sat:
        model = solver.model()
        s_val = [model.evaluate(s[i]).as_long() for i in range(11)]
        
        segments = []
        start_day = 1
        current_city = s_val[0]
        for i in range(1, 11):
            if s_val[i] != current_city:
                segments.append((start_day, i, current_city))
                start_day = i
                current_city = s_val[i]
        segments.append((start_day, 10, current_city))
        
        itinerary = []
        city_map = {0: "Mykonos", 1: "Vienna", 2: "Venice"}
        for seg in segments:
            if seg[0] == seg[1]:
                day_range_str = "Day {}".format(seg[0])
            else:
                day_range_str = "Day {}-{}".format(seg[0], seg[1])
            itinerary.append({"day_range": day_range_str, "place": city_map[seg[2]]})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()