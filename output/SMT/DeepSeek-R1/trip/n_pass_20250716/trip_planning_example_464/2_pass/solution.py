import z3
import json

def main():
    cities = ['Naples', 'Frankfurt', 'Krakow', 'Dubrovnik', 'Oslo']
    city_to_index = {city: idx for idx, city in enumerate(cities)}
    lengths = [5, 4, 5, 5, 3]  # Naples, Frankfurt, Krakow, Dubrovnik, Oslo
    
    allowed_edges = [
        (0, 3), (3, 0),  # Naples <-> Dubrovnik
        (0, 1), (1, 0),  # Naples <-> Frankfurt
        (0, 4), (4, 0),  # Naples <-> Oslo
        (1, 2), (2, 1),  # Frankfurt <-> Krakow
        (1, 3), (3, 1),  # Frankfurt <-> Dubrovnik
        (1, 4), (4, 1),  # Frankfurt <-> Oslo
        (2, 4), (4, 2),  # Krakow <-> Oslo
        (3, 4), (4, 3)   # Dubrovnik <-> Oslo
    ]
    
    s = [z3.Int(f's_{i}') for i in range(5)]
    e = [z3.Int(f'e_{i}') for i in range(5)]
    seg = [z3.Int(f'seg_{i}') for i in range(5)]
    
    solver = z3.Solver()
    
    solver.add(s[0] == 1)
    solver.add(e[4] == 18)
    
    for i in range(4):
        solver.add(s[i+1] == e[i])
    
    for i in range(5):
        solver.add(seg[i] >= 0, seg[i] < 5)
    
    solver.add(z3.Distinct(seg))
    
    for i in range(5):
        duration = z3.If(seg[i] == 0, lengths[0],
                     z3.If(seg[i] == 1, lengths[1],
                     z3.If(seg[i] == 2, lengths[2],
                     z3.If(seg[i] == 3, lengths[3], lengths[4]))))
        solver.add(e[i] == s[i] + duration - 1)
    
    for i in range(5):
        solver.add(z3.Implies(seg[i] == city_to_index['Dubrovnik'], s[i] == 5))
        solver.add(z3.Implies(seg[i] == city_to_index['Dubrovnik'], e[i] == 9))
        solver.add(z3.Implies(seg[i] == city_to_index['Oslo'], s[i] == 16))
        solver.add(z3.Implies(seg[i] == city_to_index['Oslo'], e[i] == 18))
    
    for i in range(4):
        from_city = seg[i]
        to_city = seg[i+1]
        edge_constraints = []
        for u, v in allowed_edges:
            edge_constraints.append(z3.And(from_city == u, to_city == v))
        solver.add(z3.Or(edge_constraints))
    
    if solver.check() == z3.sat:
        model = solver.model()
        seg_val = [model.evaluate(seg[i]).as_long() for i in range(5)]
        s_val = [model.evaluate(s[i]).as_long() for i in range(5)]
        e_val = [model.evaluate(e[i]).as_long() for i in range(5)]
        
        city_names = [cities[seg_val[i]] for i in range(5)]
        starts = [s_val[i] for i in range(5)]
        ends = [e_val[i] for i in range(5)]
        
        itinerary = []
        for i in range(5):
            itinerary.append({'day_range': f"Day {starts[i]}-{ends[i]}", 'place': city_names[i]})
            if i < 4:
                itinerary.append({'day_range': f"Day {ends[i]}", 'place': city_names[i]})
                itinerary.append({'day_range': f"Day {ends[i]}", 'place': city_names[i+1]})
        
        result = {'itinerary': itinerary}
        print(json.dumps(result))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == '__main__':
    main()