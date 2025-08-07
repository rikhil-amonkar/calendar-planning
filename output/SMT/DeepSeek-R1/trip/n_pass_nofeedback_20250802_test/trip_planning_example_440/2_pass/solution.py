from z3 import *
import json

def main():
    cities = ['Split', 'Helsinki', 'Reykjavik', 'Vilnius', 'Geneva']
    n_cities = len(cities)
    n_days = 12
    
    direct_flights = [
        ('Split', 'Helsinki'),
        ('Geneva', 'Split'),
        ('Geneva', 'Helsinki'),
        ('Helsinki', 'Reykjavik'),
        ('Vilnius', 'Helsinki'),
        ('Split', 'Vilnius')
    ]
    flight_set = set()
    for a, b in direct_flights:
        flight_set.add((a, b))
        flight_set.add((b, a))
    
    s = Solver()
    
    in_city = [[Bool(f'in_{d}_{c}') for c in range(n_cities)] for d in range(n_days)]
    
    for d in range(n_days):
        or_terms = [in_city[d][c] for c in range(n_cities)]
        s.add(Or(or_terms))
        
        for c1 in range(n_cities):
            for c2 in range(c1+1, n_cities):
                for c3 in range(c2+1, n_cities):
                    s.add(Not(And(in_city[d][c1], in_city[d][c2], in_city[d][c3])))
                    
    for d in range(n_days):
        for c1 in range(n_cities):
            for c2 in range(c1+1, n_cities):
                city1 = cities[c1]
                city2 = cities[c2]
                if (city1, city2) not in flight_set:
                    s.add(Not(And(in_city[d][c1], in_city[d][c2])))
    
    total_days = [0] * n_cities
    for c in range(n_cities):
        total = 0
        for d in range(n_days):
            total += If(in_city[d][c], 1, 0)
        if cities[c] == 'Split':
            s.add(total == 2)
        elif cities[c] == 'Helsinki':
            s.add(total == 2)
        elif cities[c] == 'Reykjavik':
            s.add(total == 3)
        elif cities[c] == 'Vilnius':
            s.add(total == 3)
        elif cities[c] == 'Geneva':
            s.add(total == 6)
    
    reyk_index = cities.index('Reykjavik')
    s.add(in_city[9][reyk_index])
    s.add(in_city[10][reyk_index])
    s.add(in_city[11][reyk_index])
    
    vilnius_index = cities.index('Vilnius')
    s.add(Or(in_city[6][vilnius_index], in_city[7][vilnius_index], in_city[8][vilnius_index]))
    
    for d in range(n_days - 1):
        for a in range(n_cities):
            for b in range(n_cities):
                if a != b:
                    s.add(Implies(And(in_city[d][a], in_city[d+1][b]), 
                                Or(in_city[d][b], in_city[d+1][a])))
    
    if s.check() == sat:
        model = s.model()
        itinerary_list = []
        for d in range(n_days):
            current_cities = []
            for c in range(n_cities):
                if is_true(model.eval(in_city[d][c])):
                    current_cities.append(cities[c])
            day_entry = {"day": d+1, "place": ", ".join(current_cities)}
            itinerary_list.append(day_entry)
        
        result = {"itinerary": itinerary_list}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()