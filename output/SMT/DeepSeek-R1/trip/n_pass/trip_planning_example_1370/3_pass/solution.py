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
    
    graph = set()
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
    
    for a, b in bidirectional_edges:
        a_fixed = 'Munich' if a == 'Munich' else a
        b_fixed = 'Munich' if b == 'Munich' else b
        a_fixed = 'Geneva' if a == 'Geneva' else a_fixed
        b_fixed = 'Geneva' if b == 'Geneva' else b_fixed
        graph.add((a_fixed, b_fixed))
        graph.add((b_fixed, a_fixed))
    
    for a, b in unidirectional_edges:
        a_fixed = 'Munich' if a == 'Munich' else a
        b_fixed = 'Munich' if b == 'Munich' else b
        graph.add((a_fixed, b_fixed))
    
    s = Solver()
    pos = {c: Int(f'pos_{c}') for c in cities}
    s.add(Distinct([pos[c] for c in cities]))
    for c in cities:
        s.add(pos[c] >= 0, pos[c] < 9)
    
    start_vars = {}
    for c in cities:
        total = 1
        for d in cities:
            total = total + If(pos[d] < pos[c], durations[d] - 1, 0)
        start_vars[c] = total
    
    s.add(start_vars['Santorini'] <= 29)
    s.add(start_vars['Santorini'] + durations['Santorini'] - 1 >= 25)
    s.add(start_vars['Krakow'] <= 22)
    s.add(start_vars['Krakow'] + durations['Krakow'] - 1 >= 18)
    s.add(start_vars['Paris'] <= 15)
    s.add(start_vars['Paris'] + durations['Paris'] - 1 >= 11)
    
    for a in cities:
        for b in cities:
            if a != b and (a, b) not in graph:
                s.add(Not(pos[b] == pos[a] + 1))
    
    if s.check() == sat:
        m = s.model()
        pos_val = {c: m.evaluate(pos[c]).as_long() for c in cities}
        start_val = {c: m.evaluate(start_vars[c]).as_long() for c in cities}
        end_val = {c: start_val[c] + durations[c] - 1 for c in cities}
        
        itinerary_list = []
        for day in range(1, 31):
            active_cities = []
            for c in cities:
                if start_val[c] <= day <= end_val[c]:
                    active_cities.append(c)
            active_cities_sorted = sorted(active_cities, key=lambda city: pos_val[city])
            place_str = ", ".join(active_cities_sorted)
            day_range = f"Day {day}"
            itinerary_list.append({"day_range": day_range, "place": place_str})
        
        result = {"itinerary": itinerary_list}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()