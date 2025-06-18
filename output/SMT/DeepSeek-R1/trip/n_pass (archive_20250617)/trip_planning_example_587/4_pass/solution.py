from z3 import *

def main():
    s = Solver()
    
    cities = ["Manchester", "Venice", "Istanbul", "Krakow", "Lyon"]
    req_days = [3, 7, 7, 6, 2]
    city_index = {city: idx for idx, city in enumerate(cities)}
    
    in_city = [[Bool(f'in_day{d}_{city}') for city in cities] for d in range(21)]
    
    edges = [
        ("Manchester", "Venice"),
        ("Manchester", "Istanbul"),
        ("Venice", "Istanbul"),
        ("Istanbul", "Krakow"),
        ("Venice", "Lyon"),
        ("Lyon", "Istanbul"),
        ("Manchester", "Krakow")
    ]
    allowed_pairs = set()
    for a, b in edges:
        allowed_pairs.add((a, b))
        allowed_pairs.add((b, a))
    
    for day in range(21):
        for i in range(5):
            for j in range(i + 1, 5):
                c1 = cities[i]
                c2 = cities[j]
                if (c1, c2) not in allowed_pairs:
                    s.add(Not(And(in_city[day][i], in_city[day][j])))
    
    for day in range(21):
        count = Sum([If(in_city[day][i], 1, 0) for i in range(5)])
        s.add(Or(count == 1, count == 2))
    
    for idx in range(5):
        total = Sum([If(in_city[day][idx], 1, 0) for day in range(21)])
        s.add(total == req_days[idx])
    
    manchester_idx = city_index["Manchester"]
    s.add(Or(in_city[0][manchester_idx], in_city[1][manchester_idx], in_city[2][manchester_idx]))
    
    venice_idx = city_index["Venice"]
    s.add(Or([in_city[i][venice_idx] for i in range(2, 9)]))
    
    flight_days = [Bool(f'flight_day_{d}') for d in range(21)]
    for day in range(21):
        count = Sum([If(in_city[day][i], 1, 0) for i in range(5)])
        s.add(flight_days[day] == (count == 2))
    s.add(Sum([If(flight_days[day], 1, 0) for day in range(21)]) == 4)
    
    for day in range(20):
        common_exists = Or([And(in_city[day][i], in_city[day+1][i]) for i in range(5)])
        s.add(common_exists)
        
        for j in range(5):
            new_city_j = And(in_city[day+1][j], Not(in_city[day][j]))
            k_list = []
            for k in range(5):
                if k == j:
                    continue
                if (cities[k], cities[j]) in allowed_pairs:
                    common_city_k = And(in_city[day][k], in_city[day+1][k])
                    k_list.append(common_city_k)
            if k_list:
                s.add(Implies(new_city_j, Or(k_list)))
    
    for c in range(5):
        for start in range(0, 17):
            consecutive = And([in_city[start+i][c] for i in range(6)])
            s.add(Not(consecutive))
            
    if s.check() == sat:
        m = s.model()
        schedule = []
        for day in range(21):
            current_cities = []
            for city_idx in range(5):
                if is_true(m.evaluate(in_city[day][city_idx])):
                    current_cities.append(cities[city_idx])
            schedule.append(current_cities)
        for day in range(21):
            print(f"Day {day+1}: {', '.join(schedule[day])}")
    else:
        print("No solution found")

if __name__ == '__main__':
    main()