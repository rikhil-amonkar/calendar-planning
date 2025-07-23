from z3 import *
import json

def main():
    cities = [0, 1, 2, 3, 4]
    names = {
        0: "Bucharest",
        1: "Warsaw",
        2: "Stuttgart",
        3: "Copenhagen",
        4: "Dubrovnik"
    }
    
    x = [Int('x%d' % i) for i in range(20)]
    s = Solver()
    
    for i in range(20):
        s.add(And(x[i] >= 0, x[i] <= 4))
    
    for day in range(1, 20):
        a = x[day-1]
        b = x[day]
        s.add(Or(
            a == b,
            And(a == 0, Or(b == 1, b == 3)),
            And(a == 1, Or(b == 0, b == 2, b == 3)),
            And(a == 2, Or(b == 1, b == 3)),
            And(a == 3, Or(b == 0, b == 1, b == 2, b == 4)),
            And(a == 4, b == 3)
        ))
    
    counts = [0] * 5
    for c in cities:
        total = 0
        for day in range(1, 20):
            total += If(Or(x[day-1] == c, x[day] == c), 1, 0)
        counts[c] = total
    
    s.add(counts[0] == 6)
    s.add(counts[1] == 2)
    s.add(counts[2] == 7)
    s.add(counts[3] == 3)
    s.add(counts[4] == 5)
    
    s.add(Or(x[6] == 2, x[7] == 2))
    s.add(Or(x[12] == 2, x[13] == 2))
    
    wedding_constraint = Or([Or(x[d-1] == 0, x[d] == 0) for d in range(1, 7)])
    s.add(wedding_constraint)
    
    if s.check() == sat:
        m = s.model()
        x_vals = [m.evaluate(x_i) for x_i in x]
        itinerary = []
        for day in range(1, 20):
            a_val = m.evaluate(x[day-1]).as_long()
            b_val = m.evaluate(x[day]).as_long()
            if a_val == b_val:
                itinerary.append([names[a_val]])
            else:
                itinerary.append([names[a_val], names[b_val]])
        result = {'itinerary': itinerary}
        print(json.dumps(result))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()