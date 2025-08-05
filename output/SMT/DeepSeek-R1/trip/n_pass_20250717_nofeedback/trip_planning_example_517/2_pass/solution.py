from z3 import *
import json

def main():
    cities = ["Bucharest", "Warsaw", "Stuttgart", "Copenhagen", "Dubrovnik"]
    B, W, S, C, D = 0, 1, 2, 3, 4
    
    x = [Int('x%d' % i) for i in range(20)]
    s = Solver()
    
    for i in range(20):
        s.add(And(x[i] >= 0, x[i] <= 4))
    
    for i in range(1, 20):
        prev = x[i-1]
        curr = x[i]
        s.add(Or(
            prev == curr,
            And(prev == B, Or(curr == W, curr == C)),
            And(prev == W, Or(curr == B, curr == S, curr == C)),
            And(prev == S, Or(curr == W, curr == C)),
            And(prev == C, Or(curr == B, curr == W, curr == S, curr == D)),
            And(prev == D, curr == C)
        ))
    
    counts = [0] * 5
    for c in range(5):
        total = 0
        for i in range(1, 20):
            total += If(Or(x[i-1] == c, x[i] == c), 1, 0)
        counts[c] = total
    
    s.add(counts[B] == 6)
    s.add(counts[W] == 2)
    s.add(counts[S] == 7)
    s.add(counts[C] == 3)
    s.add(counts[D] == 5)
    
    s.add(Or(x[6] == S, x[7] == S))
    s.add(Or(x[12] == S, x[13] == S))
    
    wedding_constraint = Or([Or(x[i-1] == B, x[i] == B) for i in range(1, 7)])
    s.add(wedding_constraint)
    
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(1, 20):
            start_val = m.evaluate(x[i-1]).as_long()
            end_val = m.evaluate(x[i]).as_long()
            if start_val == end_val:
                itinerary.append([cities[start_val]])
            else:
                itinerary.append([cities[start_val], cities[end_val]])
        result = {'itinerary': itinerary}
        print(json.dumps(result))
    else:
        print(json.dumps({'itinerary': []}))

if __name__ == "__main__":
    main()