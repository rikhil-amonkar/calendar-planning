import z3
import json

def main():
    city_names = ['Oslo', 'Helsinki', 'Edinburgh', 'Riga', 'Tallinn', 'Budapest', 'Vilnius', 'Porto', 'Geneva']
    durations = [2, 2, 3, 2, 5, 5, 5, 5, 4]  # Indexed by city_names order
    
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

    s = z3.Solver()
    seq = [z3.Int(f'seq_{i}') for i in range(9)]
    start = [z3.Int(f'start_{i}') for i in range(9)]
    
    s.add(z3.Distinct(seq))
    for i in range(9):
        s.add(seq[i] >= 0, seq[i] < 9)
    
    s.add(start[0] == 1)
    
    for i in range(1, 9):
        prev_city_duration = durations[seq[i-1]]
        s.add(start[i] == start[i-1] + prev_city_duration - 1)
    
    for i in range(8):
        constraints = []
        for (a, b) in allowed_edges_index:
            constraints.append(z3.And(seq[i] == a, seq[i+1] == b))
        s.add(z3.Or(constraints))
    
    tallinn_index = city_names.index('Tallinn')
    oslo_index = city_names.index('Oslo')
    
    for i in range(9):
        s.add(z3.Implies(seq[i] == tallinn_index, start[i] <= 8))
    s.add(z3.Or([z3.And(seq[i] == oslo_index, z3.Or(start[i] == 23, start[i] == 24)) for i in range(9)]))
    
    if s.check() == z3.sat:
        m = s.model()
        sol_seq = [m.evaluate(seq[i]).as_long() for i in range(9)]
        sol_start = [m.evaluate(start[i]).as_long() for i in range(9)]
        
        itinerary = []
        for day in range(1, 26):
            cities_today = []
            for i in range(9):
                city_idx = sol_seq[i]
                s_day = sol_start[i]
                duration_val = durations[city_idx]
                e_day = s_day + duration_val - 1
                if s_day <= day <= e_day:
                    cities_today.append(city_names[city_idx])
            itinerary.append({"day": day, "city": cities_today})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == '__main__':
    main()