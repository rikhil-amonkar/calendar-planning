from z3 import *
import json

def main():
    cities = ['Split', 'Helsinki', 'Reykjavik', 'Vilnius', 'Geneva']
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
    
    in_city = [[Bool(f'in_{d}_{c}') for c in cities] for d in range(n_days)]
    
    for d in range(n_days):
        s.add(Or(in_city[d]))
        for i in range(len(cities)):
            for j in range(i+1, len(cities)):
                for k in range(j+1, len(cities)):
                    s.add(Not(And(in_city[d][i], in_city[d][j], in_city[d][k])))
    
    for d in range(n_days):
        for i in range(len(cities)):
            for j in range(i+1, len(cities)):
                if (cities[i], cities[j]) not in flight_set:
                    s.add(Not(And(in_city[d][i], in_city[d][j])))
    
    total_days = {
        'Split': 2,
        'Helsinki': 2,
        'Reykjavik': 3,
        'Vilnius': 3,
        'Geneva': 6
    }
    for c_idx, city in enumerate(cities):
        total = 0
        for d in range(n_days):
            total += If(in_city[d][c_idx], 1, 0)
        s.add(total == total_days[city])
    
    reyk_index = cities.index('Reykjavik')
    s.add(in_city[9][reyk_index])
    s.add(in_city[10][reyk_index])
    s.add(in_city[11][reyk_index])
    
    vilnius_index = cities.index('Vilnius')
    s.add(Or(in_city[6][vilnius_index], in_city[7][vilnius_index], in_city[8][vilnius_index]))
    
    for d in range(n_days - 1):
        common_city = Or([And(in_city[d][i], in_city[d+1][i]) for i in range(len(cities))])
        s.add(common_city)
    
    if s.check() == sat:
        model = s.model()
        day_assignments = []
        for d in range(n_days):
            current_cities = []
            for c_idx, city in enumerate(cities):
                if is_true(model.eval(in_city[d][c_idx])):
                    current_cities.append(city)
            current_cities.sort()
            day_assignments.append(current_cities)
        
        itinerary = []
        start_day = 0
        current_set = day_assignments[0]
        for d in range(1, n_days):
            if day_assignments[d] == current_set:
                continue
            else:
                if start_day == d-1:
                    day_range = f"Day {start_day+1}"
                else:
                    day_range = f"Day {start_day+1}-{d}"
                itinerary.append({
                    'day_range': day_range,
                    'place': ', '.join(current_set)
                })
                start_day = d
                current_set = day_assignments[d]
        if start_day == n_days-1:
            day_range = f"Day {n_days}"
        else:
            day_range = f"Day {start_day+1}-{n_days}"
        itinerary.append({
            'day_range': day_range,
            'place': ', '.join(current_set)
        })
        
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()