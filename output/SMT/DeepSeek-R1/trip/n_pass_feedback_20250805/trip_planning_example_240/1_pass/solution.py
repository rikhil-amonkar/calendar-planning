from z3 import *
import json

def main():
    s = Solver()
    
    e = [Int('e%d' % i) for i in range(13)]
    
    for i in range(13):
        s.add(e[i] >= 0, e[i] <= 3)
    
    direct_flights = set()
    direct_flights.add((1, 2))  # Berlin to Tallinn
    direct_flights.add((2, 1))  # Tallinn to Berlin
    direct_flights.add((0, 2))  # Prague to Tallinn
    direct_flights.add((2, 0))  # Tallinn to Prague
    direct_flights.add((3, 2))  # Stockholm to Tallinn
    direct_flights.add((2, 3))  # Tallinn to Stockholm
    direct_flights.add((0, 3))  # Prague to Stockholm
    direct_flights.add((3, 0))  # Stockholm to Prague
    direct_flights.add((3, 1))  # Stockholm to Berlin
    direct_flights.add((1, 3))  # Berlin to Stockholm

    for i in range(1, 13):
        constraints = []
        for (a, b) in direct_flights:
            constraints.append(And(e[i-1] == a, e[i] == b))
        s.add(Implies(e[i-1] != e[i], Or(constraints)))
    
    # Total days for Prague (0)
    total0 = 0
    for i in range(0, 12): 
        total0 += If(e[i] == 0, 1, 0)
    for i in range(1, 13): 
        total0 += If(And(e[i-1] != e[i], e[i] == 0), 1, 0)
    s.add(total0 == 2)
    
    # Total days for Berlin (1)
    total1 = 0
    for i in range(0, 12): 
        total1 += If(e[i] == 1, 1, 0)
    for i in range(1, 13): 
        total1 += If(And(e[i-1] != e[i], e[i] == 1), 1, 0)
    s.add(total1 == 3)
    
    # Total days for Tallinn (2)
    total2 = 0
    for i in range(0, 12): 
        total2 += If(e[i] == 2, 1, 0)
    for i in range(1, 13): 
        total2 += If(And(e[i-1] != e[i], e[i] == 2), 1, 0)
    s.add(total2 == 5)
    
    # Total days for Stockholm (3)
    total3 = 0
    for i in range(0, 12): 
        total3 += If(e[i] == 3, 1, 0)
    for i in range(1, 13): 
        total3 += If(And(e[i-1] != e[i], e[i] == 3), 1, 0)
    s.add(total3 == 5)
    
    # Day 6: must be in Berlin (either start or end)
    s.add(Or(e[5] == 1, e[6] == 1))
    
    # Day 8: must start in Berlin and end in Tallinn
    s.add(e[7] == 1)  # start of day8 is Berlin
    s.add(e[8] == 2)  # end of day8 is Tallinn
    
    # Days 8 to 12 must end in Tallinn
    s.add(e[9] == 2)
    s.add(e[10] == 2)
    s.add(e[11] == 2)
    s.add(e[12] == 2)
    
    if s.check() == sat:
        m = s.model()
        res = [m.evaluate(e[i]).as_long() for i in range(13)]
        city_map = {0: 'Prague', 1: 'Berlin', 2: 'Tallinn', 3: 'Stockholm'}
        itinerary = []
        for day in range(1, 13):
            city_index = res[day]
            itinerary.append({"day": day, "city": city_map[city_index]})
        result_dict = {"itinerary": itinerary}
        print(json.dumps(result_dict))
    else:
        print(json.dumps({"error": "No solution found"}))

if __name__ == "__main__":
    main()