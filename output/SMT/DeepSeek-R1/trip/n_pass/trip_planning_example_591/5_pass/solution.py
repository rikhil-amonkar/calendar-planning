from z3 import *
import json

def main():
    cities = ['Stuttgart', 'Bucharest', 'Geneva', 'Valencia', 'Munich']
    durations = [2, 2, 4, 6, 7]
    city_to_idx = {city: idx for idx, city in enumerate(cities)}
    idx_to_city = {idx: city for idx, city in enumerate(cities)}
    
    allowed_edges = set()
    edges = [
        ('Geneva', 'Munich'), 
        ('Munich', 'Valencia'), 
        ('Bucharest', 'Valencia'), 
        ('Munich', 'Bucharest'), 
        ('Valencia', 'Stuttgart'), 
        ('Geneva', 'Valencia')
    ]
    for u, v in edges:
        u_idx = city_to_idx[u]
        v_idx = city_to_idx[v]
        allowed_edges.add((u_idx, v_idx))
        allowed_edges.add((v_idx, u_idx))
    
    pos = [Int(f'pos_{i}') for i in range(5)]
    start = [Int(f'start_{i}') for i in range(5)]
    city_start = [Int(f'city_start_{i}') for i in range(5)]
    
    s = Solver()
    
    for p in pos:
        s.add(And(p >= 0, p < 5))
    s.add(Distinct(pos))
    
    def duration(city_idx):
        return If(city_idx == 0, durations[0],
                If(city_idx == 1, durations[1],
                If(city_idx == 2, durations[2],
                If(city_idx == 3, durations[3],
                durations[4]))))
    
    s.add(start[0] == 1)
    
    for i in range(4):
        prev_city = pos[i]
        s.add(start[i+1] == start[i] + duration(prev_city) - 1)
    
    last_city = pos[4]
    s.add(start[4] + duration(last_city) - 1 == 17)
    
    for j in range(5):
        s.add(Or([And(pos[i] == j, city_start[j] == start[i]) for i in range(5)]))
    
    for i in range(4):
        city_i = pos[i]
        city_j = pos[i+1]
        s.add(Or([And(city_i == u, city_j == v) for (u, v) in allowed_edges]))
    
    geneva_idx = city_to_idx['Geneva']
    munich_idx = city_to_idx['Munich']
    s.add(city_start[geneva_idx] <= 4)
    s.add(city_start[munich_idx] <= 10)
    
    if s.check() == sat:
        model = s.model()
        city_start_vals = {}
        for j in range(5):
            city_start_vals[j] = model.evaluate(city_start[j]).as_long()
        
        itinerary = []
        for day in range(1, 18):
            cities_today = []
            for j in range(5):
                s_day = city_start_vals[j]
                e_day = s_day + durations[j] - 1
                if s_day <= day <= e_day:
                    cities_today.append(idx_to_city[j])
            cities_today.sort()
            itinerary.append({'day': day, 'place': ", ".join(cities_today)})
        
        print(json.dumps({'itinerary': itinerary}))
    else:
        print("No solution found")

if __name__ == '__main__':
    main()