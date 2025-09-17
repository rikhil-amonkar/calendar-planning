from z3 import *
import json

def main():
    s = Solver()
    
    cities = ['Manchester', 'Istanbul', 'Venice', 'Krakow', 'Lyon']
    n = len(cities)
    city_index = {city: i for i, city in enumerate(cities)}
    
    starts = [Int(f'start_{city}') for city in cities]
    ends = [Int(f'end_{city}') for city in cities]
    
    durations = [3, 7, 7, 6, 2]
    for i in range(n):
        s.add(ends[i] - starts[i] + 1 == durations[i])
        s.add(starts[i] >= 1, ends[i] <= 21)
    
    s.add(starts[0] <= 3)
    s.add(And(starts[2] <= 9, ends[2] >= 3))
    
    pos = [Int(f'pos_{city}') for city in cities]
    for p in pos:
        s.add(p >= 0, p < n)
    s.add(Distinct(pos))
    
    flights = [(0,2), (0,1), (2,1), (1,3), (2,4), (4,1), (0,3)]
    flight_set = set()
    for (i, j) in flights:
        flight_set.add((i, j))
        flight_set.add((j, i))
    
    def connected(i, j):
        options = []
        for (a, b) in flight_set:
            options.append(And(i == a, j == b))
        return Or(options)
    
    for k in range(n-1):
        for i in range(n):
            for j in range(n):
                if i != j:
                    cond = And(pos[i] == k, pos[j] == k+1)
                    s.add(Implies(cond, connected(i, j)))
    
    for k in range(n-1):
        for i in range(n):
            for j in range(n):
                if i != j:
                    cond = And(pos[i] == k, pos[j] == k+1)
                    s.add(Implies(cond, ends[i] == starts[j]))
    
    for i in range(n):
        s.add(Implies(pos[i] == 0, starts[i] == 1))
    
    for i in range(n):
        s.add(Implies(pos[i] == n-1, ends[i] == 21))
    
    if s.check() == sat:
        model = s.model()
        city_starts = [model.evaluate(starts[i]) for i in range(n)]
        city_ends = [model.evaluate(ends[i]) for i in range(n)]
        city_positions = [model.evaluate(pos[i]) for i in range(n)]
        
        order = [None] * n
        for i in range(n):
            p = city_positions[i].as_long()
            order[p] = cities[i]
        
        itinerary = []
        for city in order:
            idx = city_index[city]
            s_val = city_starts[idx].as_long()
            e_val = city_ends[idx].as_long()
            itinerary.append({"day_range": f"Day {s_val}-{e_val}", "place": city})
        
        print(json.dumps({"itinerary": itinerary}))
    else:
        print('No solution found')

if __name__ == '__main__':
    main()