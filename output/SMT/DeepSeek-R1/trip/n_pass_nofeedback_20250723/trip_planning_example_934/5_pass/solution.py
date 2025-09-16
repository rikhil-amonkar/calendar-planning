from z3 import *
import json

def main():
    cities = ['Brussels', 'Rome', 'Dubrovnik', 'Geneva', 'Budapest', 'Riga', 'Valencia']
    req_days = [5, 2, 3, 5, 2, 4, 2]
    
    bidirectional_pairs = [
        ('Brussels', 'Valencia'),
        ('Rome', 'Valencia'),
        ('Brussels', 'Geneva'),
        ('Rome', 'Geneva'),
        ('Dubrovnik', 'Geneva'),
        ('Valencia', 'Geneva'),
        ('Geneva', 'Budapest'),
        ('Riga', 'Brussels'),
        ('Rome', 'Budapest'),
        ('Rome', 'Brussels'),
        ('Brussels', 'Budapest'),
        ('Dubrovnik', 'Rome')
    ]
    directed_edges = [('Rome', 'Riga')]
    
    edges = set()
    for a, b in bidirectional_pairs:
        i = cities.index(a)
        j = cities.index(b)
        edges.add((i, j))
        edges.add((j, i))
    for a, b in directed_edges:
        i = cities.index(a)
        j = cities.index(b)
        edges.add((i, j))
    
    num_days = 17
    s = Solver()
    
    start = [Int(f'start_{d}') for d in range(num_days)]
    flight = [Int(f'flight_{d}') for d in range(num_days)]
    NO_FLIGHT = 7
    
    for d in range(num_days):
        s.add(0 <= start[d], start[d] <= 6)
        s.add(0 <= flight[d], flight[d] <= 7)
        s.add(If(flight[d] != NO_FLIGHT, flight[d] != start[d], True))
    
    for d in range(num_days):
        cond = (flight[d] != NO_FLIGHT)
        allowed_edges = []
        for (i, j) in edges:
            allowed_edges.append(And(start[d] == i, flight[d] == j))
        s.add(If(cond, Or(allowed_edges), True))
    
    for d in range(num_days - 1):
        s.add(If(flight[d] != NO_FLIGHT, start[d+1] == flight[d], start[d+1] == start[d]))
    
    for c in range(7):
        total = 0
        for d in range(num_days):
            in_city = Or(start[d] == c, And(flight[d] != NO_FLIGHT, flight[d] == c))
            total += If(in_city, 1, 0)
        s.add(total == req_days[c])
    
    brussels_idx = cities.index('Brussels')
    s.add(Or([start[d] == brussels_idx for d in range(6, 11)]))
    
    riga_idx = cities.index('Riga')
    s.add(Or([start[d] == riga_idx for d in range(3, 7)]))
    
    budapest_idx = cities.index('Budapest')
    s.add(Or([start[d] == budapest_idx for d in [15, 16]]))
    
    flight_count = Sum([If(flight[d] != NO_FLIGHT, 1, 0) for d in range(num_days)])
    s.add(flight_count == 6)
    
    riga_idx = cities.index('Riga')
    budapest_idx = cities.index('Budapest')
    s.add(start[0] == riga_idx)
    s.add(start[16] == budapest_idx)
    
    if s.check() == sat:
        model = s.model()
        start_vals = [model.evaluate(start[d]).as_long() for d in range(num_days)]
        
        blocks = []
        d = 0
        while d < num_days:
            current_city_idx = start_vals[d]
            j = d
            while j < num_days and start_vals[j] == current_city_idx:
                j += 1
            start_day = d + 1
            end_day = j
            if end_day - d == 1:
                day_range_str = f"Day {start_day}"
            else:
                day_range_str = f"Day {start_day}-{end_day}"
            blocks.append({'day_range': day_range_str, 'place': cities[current_city_idx]})
            d = j
        
        result = {"itinerary": blocks}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()