from z3 import *
import json

def main():
    city_names = ['Reykjavik', 'Stockholm', 'Porto', 'Nice', 'Venice', 'Vienna', 'Split', 'Copenhagen']
    city_durations = [2, 2, 5, 3, 4, 3, 3, 2]
    events = {
        'Reykjavik': (3, 4),
        'Stockholm': (4, 5),
        'Porto': (13, 17),
        'Vienna': (11, 13)
    }
    direct_flights = [
        ('Copenhagen', 'Vienna'), ('Nice', 'Stockholm'), ('Split', 'Copenhagen'),
        ('Nice', 'Reykjavik'), ('Nice', 'Porto'), ('Reykjavik', 'Vienna'),
        ('Stockholm', 'Copenhagen'), ('Nice', 'Venice'), ('Nice', 'Vienna'),
        ('Reykjavik', 'Copenhagen'), ('Nice', 'Copenhagen'), ('Stockholm', 'Vienna'),
        ('Venice', 'Vienna'), ('Copenhagen', 'Porto'), ('Reykjavik', 'Stockholm'),
        ('Stockholm', 'Split'), ('Split', 'Vienna'), ('Copenhagen', 'Venice'),
        ('Vienna', 'Porto')
    ]
    
    n = len(city_names)
    connectivity = [[0] * n for _ in range(n)]
    for flight in direct_flights:
        city1, city2 = flight
        idx1 = city_names.index(city1)
        idx2 = city_names.index(city2)
        connectivity[idx1][idx2] = 1
        connectivity[idx2][idx1] = 1
        
    allowed_pairs = []
    for i in range(n):
        for j in range(n):
            if connectivity[i][j] == 1 and i != j:
                allowed_pairs.append((i, j))
                
    solver = Solver()
    
    order = [Int('order_%d' % i) for i in range(n)]
    start_first = Int('start_first')
    
    for i in range(n):
        solver.add(order[i] >= 0, order[i] < n)
    solver.add(Distinct(order))
    
    def get_duration(idx):
        return If(idx == 0, city_durations[0],
               If(idx == 1, city_durations[1],
               If(idx == 2, city_durations[2],
               If(idx == 3, city_durations[3],
               If(idx == 4, city_durations[4],
               If(idx == 5, city_durations[5],
               If(idx == 6, city_durations[6],
               city_durations[7]))))))
    
    start_days = [Int('start_day_%d' % i) for i in range(n)]
    solver.add(start_days[0] == start_first)
    
    for i in range(1, n):
        solver.add(start_days[i] == start_days[i-1] + get_duration(order[i-1]) - 1)
    
    solver.add(start_first >= 1)
    solver.add(start_days[n-1] + get_duration(order[n-1]) - 1 <= 17)
    
    for city, (event_start, event_end) in events.items():
        city_idx = city_names.index(city)
        conditions = []
        for i in range(n):
            dur = city_durations[city_idx]
            start_day = start_days[i]
            end_day = start_day + dur - 1
            conditions.append(And(order[i] == city_idx, start_day <= event_end, end_day >= event_start))
        solver.add(Or(conditions))
        
    for k in range(n-1):
 conds = []
        for (i, j) in allowed_pairs:
            conds.append(And(order[k] == i, order[k+1] == j))
        solver.add(Or(conds))
        
    if solver.check() == sat:
        model = solver.model()
        order_val = [model.evaluate(order[i]).as_long() for i in range(n)]
        start_first_val = model.evaluate(start_first).as_long()
        
        start_days_val = [0] * n
        start_days_val[0] = start_first_val
        for i in range(1, n):
            prev_city_idx = order_val[i-1]
            dur_prev = city_durations[prev_city_idx]
            start_days_val[i] = start_days_val[i-1] + dur_prev - 1
            
        itinerary = []
        for i in range(n):
            city_idx = order_val[i]
            city_name = city_names[city_idx]
            start_day = start_days_val[i]
            end_day = start_day + city_durations[city_idx] - 1
            day_range = f"Day {start_day}-{end_day}"
            itinerary.append({"day_range": day_range, "place": city_name})
            
        print(json.dumps({"itinerary": itinerary}))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()