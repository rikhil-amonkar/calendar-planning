import z3

def main():
    cities = ["Tallinn", "Prague", "Lisbon", "Copenhagen", "Dubrovnik", "Stockholm", "Split", "Lyon"]
    dur_dict = {
        "Tallinn": 2,
        "Prague": 3,
        "Lisbon": 2,
        "Copenhagen": 5,
        "Dubrovnik": 5,
        "Stockholm": 4,
        "Split": 3,
        "Lyon": 2
    }
    edges = [
        ("Dubrovnik", "Stockholm"),
        ("Lisbon", "Copenhagen"),
        ("Lisbon", "Lyon"),
        ("Copenhagen", "Stockholm"),
        ("Copenhagen", "Split"),
        ("Prague", "Stockholm"),
        ("Tallinn", "Stockholm"),
        ("Prague", "Lyon"),
        ("Lisbon", "Stockholm"),
        ("Prague", "Lisbon"),
        ("Stockholm", "Split"),
        ("Prague", "Copenhagen"),
        ("Split", "Lyon"),
        ("Copenhagen", "Dubrovnik"),
        ("Prague", "Split"),
        ("Tallinn", "Copenhagen"),
        ("Tallinn", "Prague")
    ]
    edge_set = set()
    for u, v in edges:
        edge_set.add((u, v))
        edge_set.add((v, u))
    
    s = z3.Solver()
    n = 8
    p = [z3.Int(f'p_{i}') for i in range(n)]
    
    for i in range(n):
        s.add(p[i] >= 0)
        s.add(p[i] < n)
    s.add(z3.Distinct(p))
    
    idx_Tallinn = cities.index("Tallinn")
    idx_Lyon = cities.index("Lyon")
    idx_Lisbon = cities.index("Lisbon")
    s.add(p[0] == idx_Tallinn)
    s.add(p[7] == idx_Lyon)
    s.add(p[2] == idx_Lisbon)
    
    start_days = [z3.Int(f's_{i}') for i in range(n)]
    s.add(start_days[0] == 1)
    for i in range(1, n):
        prev_city_idx = p[i-1]
        prev_city = cities[prev_city_idx]
        prev_dur = dur_dict[prev_city]
        s.add(start_days[i] == start_days[i-1] + prev_dur - 1)
    
    last_city_idx = p[7]
    last_city = cities[last_city_idx]
    last_dur = dur_dict[last_city]
    s.add(start_days[7] + last_dur - 1 == 19)
    
    s.add(start_days[2] == 4)
    
    idx_Stockholm = cities.index("Stockholm")
    for i in range(n):
        is_stockholm = z3.If(p[i] == idx_Stockholm, z3.And(start_days[i] <= 16, start_days[i] >= 10), True)
        s.add(is_stockholm)
    
    for i in range(n-1):
        city_i = p[i]
        city_j = p[i+1]
        edge_exists = z3.BoolVal(False)
        for u in range(len(cities)):
            for v in range(len(cities)):
                if (cities[u], cities[v]) in edge_set:
                    edge_exists = z3.Or(edge_exists, z3.And(city_i == u, city_j == v))
        s.add(edge_exists)
    
    if s.check() == z3.sat:
        model = s.model()
        order = [model.evaluate(p[i]).as_long() for i in range(n)]
        start_vals = [model.evaluate(start_days[i]).as_long() for i in range(n)]
        
        itinerary = []
        for i in range(n):
            city_name = cities[order[i]]
            start = start_vals[i]
            duration = dur_dict[city_name]
            end = start + duration - 1
            
            itinerary.append({"day_range": f"Day {start}-{end}", "place": city_name})
            if i < n-1:
                next_city_name = cities[order[i+1]]
                itinerary.append({"day_range": f"Day {end}", "place": city_name})
                itinerary.append({"day_range": f"Day {end}", "place": next_city_name})
        
        result = {"itinerary": itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()