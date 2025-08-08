import json
from z3 import *

def main():
    cities = ["Valencia", "Manchester", "Naples", "Oslo", "Vilnius", "Frankfurt"]
    n = len(cities)
    idx = { city: i for i, city in enumerate(cities) }
    req = [4, 4, 4, 3, 2, 4]
    
    direct_flights_list = [
        ("Valencia", "Frankfurt"),
        ("Manchester", "Frankfurt"),
        ("Naples", "Manchester"),
        ("Naples", "Frankfurt"),
        ("Naples", "Oslo"),
        ("Oslo", "Frankfurt"),
        ("Vilnius", "Frankfurt"),
        ("Oslo", "Vilnius"),
        ("Manchester", "Oslo"),
        ("Valencia", "Naples")
    ]
    
    allowed_pairs = set()
    for a, b in direct_flights_list:
        i = idx[a]
        j = idx[b]
        allowed_pairs.add((i, j))
        allowed_pairs.add((j, i))
    
    allowed_matrix = [[False] * n for _ in range(n)]
    for i in range(n):
        for j in range(n):
            if (i, j) in allowed_pairs:
                allowed_matrix[i][j] = True
                
    solver = Solver()
    
    pos = [Int('pos_%s' % city) for city in cities]
    for i in range(n):
        solver.add(pos[i] >= 0, pos[i] < n)
    solver.add(Distinct(pos))
    
    start = [Int('start_%s' % city) for city in cities]
    end = [Int('end_%s' % city) for city in cities]
    
    frankfurt_idx = idx["Frankfurt"]
    vilnius_idx = idx["Vilnius"]
    solver.add(start[frankfurt_idx] == 13)
    solver.add(end[frankfurt_idx] == 16)
    solver.add(start[vilnius_idx] == 12)
    solver.add(end[vilnius_idx] == 13)
    solver.add(pos[vilnius_idx] + 1 == pos[frankfurt_idx])
    
    for i in range(n):
        solver.add(end[i] == start[i] + req[i] - 1)
    
    for i in range(n):
        solver.add(Implies(pos[i] == 0, start[i] == 1))
        solver.add(Implies(pos[i] == n-1, end[i] == 16))
    
    for k in range(n-1):
        for i in range(n):
            for j in range(n):
                if i == j:
                    continue
                solver.add(Implies(And(pos[i] == k, pos[j] == k+1), end[i] == start[j]))
    
    for i in range(n):
        for j in range(n):
            if i != j:
                if not allowed_matrix[i][j]:
                    solver.add(Not(And(pos[i] + 1 == pos[j])))
    
    oslo_idx = idx["Oslo"]
    solver.add(pos[oslo_idx] == 3)
    
    valencia_idx = idx["Valencia"]
    manchester_idx = idx["Manchester"]
    naples_idx = idx["Naples"]
    first_three = [valencia_idx, manchester_idx, naples_idx]
    for i in first_three:
        solver.add(Or(pos[i] == 0, pos[i] == 1, pos[i] == 2))
    solver.add(Distinct([pos[valencia_idx], pos[manchester_idx], pos[naples_idx]]))
    
    if solver.check() == sat:
        model = solver.model()
        itinerary_list = []
        for d in range(1, 17):
            cities_on_day = []
            for i in range(n):
                start_val = model.eval(start[i]).as_long()
                end_val = model.eval(end[i]).as_long()
                if start_val <= d <= end_val:
                    cities_on_day.append(cities[i])
            if not cities_on_day:
                city_str = ""
            else:
                pos_vals = []
                for city in cities_on_day:
                    i_city = idx[city]
                    pos_val = model.eval(pos[i_city]).as_long()
                    pos_vals.append((pos_val, city))
                pos_vals.sort(key=lambda x: x[0])
                city_str = ",".join(city for (_, city) in pos_vals)
            itinerary_list.append({"day": d, "city": city_str})
        
        result = {'itinerary': itinerary_list}
        print(json.dumps(result))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()