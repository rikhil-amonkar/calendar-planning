from z3 import *
import json

def main():
    city_names = ['Oslo', 'Helsinki', 'Edinburgh', 'Riga', 'Tallinn', 'Budapest', 'Vilnius', 'Porto', 'Geneva']
    days_dict = {
        'Oslo': 2,
        'Helsinki': 2,
        'Edinburgh': 3,
        'Riga': 2,
        'Tallinn': 5,
        'Budapest': 5,
        'Vilnius': 5,
        'Porto': 5,
        'Geneva': 4
    }
    
    flights_str = [
        "Porto and Oslo",
        "Edinburgh and Budapest",
        "Edinburgh and Geneva",
        "from Riga to Tallinn",
        "Edinburgh and Porto",
        "Vilnius and Helsinki",
        "from Tallinn to Vilnius",
        "Riga and Oslo",
        "Geneva and Oslo",
        "Edinburgh and Oslo",
        "Edinburgh and Helsinki",
        "Vilnius and Oslo",
        "Riga and Helsinki",
        "Budapest and Geneva",
        "Helsinki and Budapest",
        "Helsinki and Oslo",
        "Edinburgh and Riga",
        "Tallinn and Helsinki",
        "Geneva and Porto",
        "Budapest and Oslo",
        "Helsinki and Geneva",
        "from Riga to Vilnius",
        "Tallinn and Oslo"
    ]
    
    allowed_edges = set()
    for s in flights_str:
        if s.startswith('from '):
            parts = s.split()
            A = parts[1]
            B = parts[3]
            allowed_edges.add((A, B))
        else:
            parts = s.split(' and ')
            A = parts[0].strip()
            B = parts[1].strip()
            allowed_edges.add((A, B))
            allowed_edges.add((B, A))
    
    allowed_edges_index = set()
    for (a, b) in allowed_edges:
        try:
            idx_a = city_names.index(a)
            idx_b = city_names.index(b)
            allowed_edges_index.add((idx_a, idx_b))
        except:
            continue
    
    s = Solver()
    seq = [Int(f'seq_{i}') for i in range(9)]
    start = [Int(f'start_{i}') for i in range(9)]
    
    s.add(Distinct(seq))
    for i in range(9):
        s.add(seq[i] >= 0, seq[i] < 9)
    
    s.add(start[0] == 1)
    
    days_arr = Array('days_arr', IntSort(), IntSort())
    for idx, city in enumerate(city_names):
        days_arr = Store(days_arr, idx, days_dict[city])
    
    for i in range(1, 9):
        prev_days = days_arr[seq[i-1]]
        s.add(start[i] == start[i-1] + prev_days - 1)
    
    for i in range(8):
        constraints = []
        for (a, b) in allowed_edges_index:
            constraints.append(And(seq[i] == a, seq[i+1] == b))
        s.add(Or(constraints))
    
    tallinn_index = city_names.index('Tallinn')
    oslo_index = city_names.index('Oslo')
    for i in range(9):
        s.add(If(seq[i] == tallinn_index, start[i] <= 8, True))
        s.add(If(seq[i] == oslo_index, And(start[i] >= 23, start[i] <= 24), True))
    
    if s.check() == sat:
        m = s.model()
        sol_seq = [m.evaluate(seq[i]).as_long() for i in range(9)]
        sol_start = [m.evaluate(start[i]).as_long() for i in range(9)]
        
        itinerary = []
        for day in range(1, 26):
            cities_today = []
            for pos in range(9):
                city_idx = sol_seq[pos]
                s_day = sol_start[pos]
                duration = days_dict[city_names[city_idx]]
                e_day = s_day + duration - 1
                if s_day <= day <= e_day:
                    cities_today.append(city_names[city_idx])
            itinerary.append({"day": day, "city": cities_today})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == '__main__':
    main()