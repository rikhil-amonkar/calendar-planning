from z3 import *
import json

def main():
    cities = ['Santorini', 'Krakow', 'Paris', 'Vilnius', 'Munich', 'Geneva', 'Amsterdam', 'Budapest', 'Split']
    durations = {
        'Santorini': 5,
        'Krakow': 5,
        'Paris': 5,
        'Vilnius': 3,
        'Munich': 5,
        'Geneva': 2,
        'Amsterdam': 4,
        'Budapest': 5,
        'Split': 4
    }
    
    bidirectional_edges = [
        ('Paris', 'Krakow'), ('Paris', 'Amsterdam'), ('Paris', 'Split'),
        ('Paris', 'Geneva'), ('Amsterdam', 'Geneva'), ('Munich', 'Split'),
        ('Split', 'Krakow'), ('Munich', 'Amsterdam'), ('Budapest', 'Amsterdam'),
        ('Split', 'Geneva'), ('Vilnius', 'Split'), ('Munich', 'Geneva'),
        ('Munich', 'Krakow'), ('Vilnius', 'Amsterdam'), ('Budapest', 'Paris'),
        ('Krakow', 'Amsterdam'), ('Vilnius', 'Paris'), ('Budapest', 'Geneva'),
        ('Split', 'Amsterdam'), ('Santorini', 'Geneva'), ('Amsterdam', 'Santorini'),
        ('Munich', 'Budapest'), ('Munich', 'Paris')
    ]
    unidirectional_edges = [
        ('Vilnius', 'Munich'),
        ('Krakow', 'Vilnius')
    ]
    
    directed_edges = set()
    for a, b in bidirectional_edges:
        directed_edges.add((a, b))
        directed_edges.add((b, a))
    for a, b in unidirectional_edges:
        directed_edges.add((a, b))
    
    s = Solver()
    
    pos_vars = {c: Int(f'pos_{c}') for c in cities}
    s.add(Distinct([pos_vars[c] for c in cities]))
    for c in cities:
        s.add(pos_vars[c] >= 0, pos_vars[c] < 9)
    
    start_vars = {}
    for c in cities:
        total = 1
        for other in cities:
            if other == c:
                continue
            total = total + If(pos_vars[other] < pos_vars[c], durations[other] - 1, 0)
        start_vars[c] = total
    
    end_vars = {c: start_vars[c] + durations[c] - 1 for c in cities}
    
    s.add(start_vars['Santorini'] <= 29, end_vars['Santorini'] >= 25)
    s.add(start_vars['Krakow'] <= 22, end_vars['Krakow'] >= 18)
    s.add(start_vars['Paris'] <= 15, end_vars['Paris'] >= 11)
    
    for c1 in cities:
        for c2 in cities:
            if c1 == c2:
                continue
            cond = (pos_vars[c1] + 1 == pos_vars[c2])
            if (c1, c2) not in directed_edges:
                s.add(Not(cond))
    
    if s.check() == sat:
        m = s.model()
        solution_pos = {}
        solution_start = {}
        solution_end = {}
        for c in cities:
            solution_pos[c] = m.evaluate(pos_vars[c]).as_long()
            solution_start[c] = m.evaluate(start_vars[c]).as_long()
            solution_end[c] = solution_start[c] + durations[c] - 1
        
        itinerary_list = []
        for day in range(1, 31):
            active_cities = []
            for c in cities:
                if solution_start[c] <= day <= solution_end[c]:
                    active_cities.append(c)
            active_cities_sorted = sorted(active_cities, key=lambda city: solution_pos[city])
            place_str = ", ".join(active_cities_sorted)
            itinerary_list.append({"day": day, "place": place_str})
        
        result = {"itinerary": itinerary_list}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()