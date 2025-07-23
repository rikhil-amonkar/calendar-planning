import json
from z3 import *

def main():
    n = 23
    cities = ["Lyon", "Paris", "Riga", "Berlin", "Stockholm", "Zurich", "Nice", "Seville", "Milan", "Naples"]
    city_to_id = {name: idx for idx, name in enumerate(cities)}
    
    allowed_pairs_list = [
        (1,4), (4,1),
        (7,1), (1,7),
        (9,5), (5,9),
        (6,2), (2,6),
        (3,8), (8,3),
        (1,5), (5,1),
        (1,6), (6,1),
        (8,1), (1,8),
        (8,2), (2,8),
        (1,0), (0,1),
        (8,9), (9,8),
        (1,2), (2,1),
        (3,4), (4,3),
        (4,2), (2,4),
        (6,5), (5,6),
        (8,5), (5,8),
        (0,6), (6,0),
        (5,4), (4,5),
        (5,2), (2,5),
        (3,9), (9,3),
        (8,4), (4,8),
        (3,5), (5,3),
        (8,7), (7,8),
        (1,9), (9,1),
        (3,2), (2,3),
        (6,4), (4,6),
        (3,1), (1,3),
        (6,9), (9,6),
        (3,6), (6,3)
    ]

    s = Solver()
    s.set("timeout", 300000)

    c1 = Int('c1')
    d = [Int('d_%d' % i) for i in range(23)]

    for var in [c1] + d:
        s.add(And(var >= 0, var <= 9))

    # Flight constraints for day1
    s.add(If(c1 != d[0],
             Or([And(c1 == p0, d[0] == p1) for (p0, p1) in allowed_pairs_list]),
             True
            ))
    
    for i in range(22):
        s.add(If(d[i] != d[i+1],
                 Or([And(d[i] == p0, d[i+1] == p1) for (p0, p1) in allowed_pairs_list]),
                 True
                ))

    counts = [0] * 10
    for x in range(10):
        total = 0
        total += If(c1 == x, 1, 0)
        total += If(And(c1 != d[0], d[0] == x), 1, 0)
        for j in range(22):
            total += If(d[j] == x, 1, 0)
            total += If(And(d[j] != d[j+1], d[j+1] == x), 1, 0)
        counts[x] = total

    s.add(counts[0] == 3)   # Lyon
    s.add(counts[1] == 5)   # Paris
    s.add(counts[2] == 2)   # Riga
    s.add(counts[3] == 2)   # Berlin
    s.add(counts[4] == 3)   # Stockholm
    s.add(counts[5] == 5)   # Zurich
    s.add(counts[6] == 2)   # Nice
    s.add(counts[7] == 3)   # Seville
    s.add(counts[8] == 3)   # Milan
    s.add(counts[9] == 4)   # Naples

    # Event constraints
    s.add(Or(c1 == 3, And(c1 != 3, d[0] == 3)))  # Berlin on day1
    s.add(Or(d[0] == 3, And(d[0] != d[1], d[1] == 3)))  # Berlin on day2
    s.add(Or(d[18] == 4, And(d[18] != d[19], d[19] == 4)))  # Stockholm on day20
    s.add(Or(d[19] == 4, And(d[19] != d[20], d[20] == 4)))  # Stockholm on day21
    s.add(Or(d[20] == 4, And(d[20] != d[21], d[21] == 4)))  # Stockholm on day22
    s.add(Or(d[10] == 6, And(d[10] != d[11], d[11] == 6)))  # Nice on day12
    s.add(Or(d[11] == 6, And(d[11] != d[12], d[12] == 6)))  # Nice on day13

    if s.check() == sat:
        m = s.model()
        c1_val = m.eval(c1).as_long()
        d_vals = [m.eval(d_i).as_long() for d_i in d]
        
        itinerary = []
        itinerary.append({"day": 1, "place": cities[c1_val]})
        if c1_val != d_vals[0]:
            itinerary.append({"day": 1, "place": cities[d_vals[0]]})
        
        for day in range(2, 24):
            idx = day - 2
            start_city = d_vals[idx]
            itinerary.append({"day": day, "place": cities[start_city]})
            if idx < 22:
                end_city = d_vals[idx+1]
                if start_city != end_city:
                    itinerary.append({"day": day, "place": cities[end_city]})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()