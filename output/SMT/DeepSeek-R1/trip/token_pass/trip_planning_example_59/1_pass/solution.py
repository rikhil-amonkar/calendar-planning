import json
from z3 import Solver, Bool, Or, And, Not, Sum, If, sat

def main():
    s = Solver()
    days = 16
    cities = ['Bucharest', 'Lyon', 'Porto']
    B = [Bool(f"B_{i}") for i in range(1, days+1)]
    L = [Bool(f"L_{i}") for i in range(1, days+1)]
    P = [Bool(f"P_{i}") for i in range(1, days+1)]
    
    for i in range(days):
        s.add(Or(
            And(B[i], Not(L[i]), Not(P[i])),
            And(Not(B[i]), L[i], Not(P[i])),
            And(Not(B[i]), Not(L[i]), P[i]),
            And(B[i], L[i], Not(P[i])),
            And(Not(B[i]), L[i], P[i])
        ))
    
    s.add(Sum([If(B[i], 1, 0) for i in range(days)]) == 7)
    s.add(Sum([If(L[i], 1, 0) for i in range(days)]) == 7)
    s.add(Sum([If(P[i], 1, 0) for i in range(days)]) == 4)
    s.add(Or([B[i] for i in range(7)]))
    s.add(And(B[0], Not(L[0]), Not(P[0])))
    s.add(And(Not(B[15]), Not(L[15]), P[15]))
    
    if s.check() == sat:
        m = s.model()
        b_days = [m.evaluate(B[i]) for i in range(days)]
        l_days = [m.evaluate(L[i]) for i in range(days)]
        p_days = [m.evaluate(P[i]) for i in range(days)]
        
        segments = []
        current_city = None
        start_day = 1
        for day in range(1, days+1):
            idx = day-1
            if b_days[idx] == True:
                city = 'Bucharest'
            elif l_days[idx] == True:
                city = 'Lyon'
            elif p_days[idx] == True:
                city = 'Porto'
            else:
                continue
                
            if current_city is None:
                current_city = city
                start_day = day
            elif city != current_city:
                segments.append({'day_range': f'Day {start_day}-{day-1}', 'place': current_city})
                current_city = city
                start_day = day
        segments.append({'day_range': f'Day {start_day}-{days}', 'place': current_city})
        
        result = {'itinerary': segments}
        print(json.dumps(result))
    else:
        print('{"itinerary": []}')

if __name__ == '__main__':
    main()