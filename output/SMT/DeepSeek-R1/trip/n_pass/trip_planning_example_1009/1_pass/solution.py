from z3 import *
import json

def main():
    cities = ["Riga", "Manchester", "Bucharest", "Florence", "Vienna", "Istanbul", "Reykjavik", "Stuttgart"]
    city_to_index = {city: idx for idx, city in enumerate(cities)}
    
    edges_str = [
        ("Bucharest", "Vienna"),
        ("Reykjavik", "Vienna"),
        ("Manchester", "Vienna"),
        ("Manchester", "Riga"),
        ("Riga", "Vienna"),
        ("Istanbul", "Vienna"),
        ("Vienna", "Florence"),
        ("Stuttgart", "Vienna"),
        ("Riga", "Bucharest"),
        ("Istanbul", "Riga"),
        ("Stuttgart", "Istanbul"),
        ("Reykjavik", "Stuttgart"),
        ("Istanbul", "Bucharest"),
        ("Manchester", "Istanbul"),
        ("Manchester", "Bucharest"),
        ("Stuttgart", "Manchester")
    ]
    
    directed_edges = set()
    for a, b in edges_str:
        i = city_to_index[a]
        j = city_to_index[b]
        directed_edges.add((i, j))
        directed_edges.add((j, i))
    
    n_cities = len(cities)
    allowed = [[False] * n_cities for _ in range(n_cities)]
    for i in range(n_cities):
        allowed[i][i] = True
    for (i, j) in directed_edges:
        allowed[i][j] = True
    
    n_days = 23
    c = [Int(f'c{i}') for i in range(n_days + 1)]
    
    s = Solver()
    
    for i in range(n_days + 1):
        s.add(And(c[i] >= 0, c[i] < n_cities))
    
    istanbul_idx = city_to_index["Istanbul"]
    bucharest_idx = city_to_index["Bucharest"]
    
    s.add(c[12] == istanbul_idx)
    s.add(c[16] == bucharest_idx)
    s.add(c[17] == bucharest_idx)
    s.add(c[18] == bucharest_idx)
    s.add(c[19] != bucharest_idx)
    s.add(c[13] != istanbul_idx)
    
    for i in [0] + list(range(1, 12)) + list(range(13, n_days + 1)):
        s.add(c[i] != istanbul_idx)
    
    for i in [0] + list(range(1, 16)) + list(range(20, n_days + 1)):
        s.add(c[i] != bucharest_idx)
    
    flight_ok = Function('flight_ok', IntSort(), IntSort(), BoolSort())
    for i in range(n_cities):
        for j in range(n_cities):
            s.add(flight_ok(i, j) == allowed[i][j])
    
    for d in range(1, n_days + 1):
        s.add(flight_ok(c[d - 1], c[d]))
    
    counts = [0] * n_cities
    for city_idx in range(n_cities):
        total = 0
        for d in range(1, n_days + 1):
            cond = Or(c[d - 1] == city_idx, c[d] == city_idx)
            total = total + If(cond, 1, 0)
        counts[city_idx] = total
    
    s.add(counts[city_to_index["Riga"]] == 4)
    s.add(counts[city_to_index["Manchester"]] == 5)
    s.add(counts[city_to_index["Bucharest"]] == 4)
    s.add(counts[city_to_index["Florence"]] == 4)
    s.add(counts[city_to_index["Vienna"]] == 2)
    s.add(counts[city_to_index["Istanbul"]] == 2)
    s.add(counts[city_to_index["Reykjavik"]] == 4)
    s.add(counts[city_to_index["Stuttgart"]] == 5)
    
    if s.check() == sat:
        model = s.model()
        itinerary_list = []
        for day in range(1, n_days + 1):
            city_idx = model.evaluate(c[day])
            if city_idx.as_long() in range(n_cities):
                city_name = cities[city_idx.as_long()]
                itinerary_list.append({"day": day, "place": city_name})
        result = {"itinerary": itinerary_list}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()