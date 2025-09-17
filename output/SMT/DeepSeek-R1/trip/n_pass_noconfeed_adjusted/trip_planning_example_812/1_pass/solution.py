from z3 import *
import json

def main():
    # Define city codes
    cities = ['Paris', 'Florence', 'Vienna', 'Porto', 'Munich', 'Nice', 'Warsaw']
    city_code = {c: i for i, c in enumerate(cities)}
    required_days = {
        city_code['Paris']: 5,
        city_code['Florence']: 3,
        city_code['Vienna']: 2,
        city_code['Porto']: 3,
        city_code['Munich']: 5,
        city_code['Nice']: 5,
        city_code['Warsaw']: 3
    }
    
    direct_flights_set = set()
    connections = [
        (0,1), (0,6), (0,2), (0,5), (0,4),
        (1,2), (1,4),
        (2,4), (2,3), (2,6), (2,5),
        (4,6), (4,5),
        (3,4), (3,5), (3,6), (3,0),
        (6,5)
    ]
    for a, b in connections:
        direct_flights_set.add((a, b))
        direct_flights_set.add((b, a))
    
    x = [Int(f'x_{i}') for i in range(20)]
    solver = Solver()
    
    for i in range(20):
        solver.add(And(x[i] >= 0, x[i] < 7))
    
    solver.add(x[0] == city_code['Porto'])
    solver.add(x[1] == city_code['Porto'])
    solver.add(x[2] == city_code['Porto'])
    solver.add(x[12] == city_code['Warsaw'])
    solver.add(x[13] == city_code['Warsaw'])
    solver.add(x[14] == city_code['Warsaw'])
    solver.add(x[18] == city_code['Vienna'])
    solver.add(x[19] == city_code['Vienna'])
    
    D = [0] * 7
    T_out = [0] * 7
    T_in = [0] * 7
    
    for c in range(7):
        D[c] = Sum([If(x[i] == c, 1, 0) for i in range(20)])
        T_out[c] = Sum([If(And(x[i] == c, i < 19, x[i] != x[i+1]), 1, 0) for i in range(19)])
        T_in[c] = Sum([If(And(x[i] == c, i > 0, x[i-1] != x[i]), 1, 0) for i in range(1, 20)])
    
    for c in range(7):
        solver.add(D[c] + T_out[c] + T_in[c] == required_days[c])
    
    for i in range(19):
        solver.add(If(x[i] != x[i+1], 
                     Or([And(x[i] == a, x[i+1] == b) for (a, b) in direct_flights_set]), 
                     True))
    
    if solver.check() == sat:
        model = solver.model()
        assignment = [model.evaluate(x[i]).as_long() for i in range(20)]
        itinerary = []
        start = 0
        current_city = assignment[0]
        for i in range(1, 20):
            if assignment[i] != current_city:
                end = i
                itinerary.append({
                    'day_range': f"Day {start+1}-{end}",
                    'place': cities[current_city]
                })
                start = i
                current_city = assignment[i]
        itinerary.append({
            'day_range': f"Day {start+1}-20",
            'place': cities[current_city]
        })
        print(json.dumps({'itinerary': itinerary}))
    else:
        print('{"itinerary": []}')

if __name__ == '__main__':
    main()