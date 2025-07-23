import json
from z3 import *

def main():
    cities = ["Krakow", "Stockholm", "Hamburg", "Florence", "Istanbul", "Oslo", "Vilnius", "Santorini", "Munich", "Frankfurt"]
    durations = [5, 3, 5, 2, 5, 5, 5, 2, 5, 4]
    
    allowed_list = [
        (5,1), (1,5),
        (0,9), (9,0),
        (0,4), (4,0),
        (8,1), (1,8),
        (2,1), (1,2),
        (0,6),
        (5,4), (4,5),
        (4,1), (1,4),
        (5,0), (0,5),
        (6,4), (4,6),
        (5,6), (6,5),
        (9,4), (4,9),
        (5,9), (9,5),
        (8,2), (2,8),
        (3,8),
        (0,8), (8,0),
        (2,4), (4,2),
        (9,1), (1,9),
        (1,7),
        (9,8), (8,9),
        (5,2), (2,5),
        (7,5),
        (0,1), (1,0),
        (6,8),
        (9,2), (2,9)
    ]
    
    s = Solver()
    
    order = [Int('c_%d' % i) for i in range(10)]
    starts = [Int('start_%d' % i) for i in range(10)]
    ends = [Int('end_%d' % i) for i in range(10)]
    
    for i in range(10):
        s.add(order[i] >= 0, order[i] <= 9)
    s.add(Distinct(order))
    
    s.add(starts[0] == 1)
    s.add(ends[0] == starts[0] + durations[order[0]] - 1)
    
    for i in range(1, 10):
        s.add(starts[i] == ends[i-1])
        s.add(ends[i] == starts[i] + durations[order[i]] - 1)
    
    for k in range(10):
        s.add(If(order[k] == 0, And(starts[k] <= 5, ends[k] >= 9), True))
        s.add(If(order[k] == 4, And(starts[k] <= 25, ends[k] >= 29), True))
    
    for i in range(9):
        disj = []
        for (a, b) in allowed_list:
            disj.append(And(order[i] == a, order[i+1] == b))
        s.add(Or(disj))
    
    if s.check() == sat:
        m = s.model()
        order_val = [m.evaluate(order[i]).as_long() for i in range(10)]
        starts_val = [m.evaluate(starts[i]).as_long() for i in range(10)]
        ends_val = [m.evaluate(ends[i]).as_long() for i in range(10)]
        
        itinerary_list = []
        for day in range(1, 33):
            for k in range(10):
                if starts_val[k] <= day <= ends_val[k]:
                    city_name = cities[order_val[k]]
                    itinerary_list.append({"day": day, "city": city_name})
        
        result = {"itinerary": itinerary_list}
        print(json.dumps(result))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()