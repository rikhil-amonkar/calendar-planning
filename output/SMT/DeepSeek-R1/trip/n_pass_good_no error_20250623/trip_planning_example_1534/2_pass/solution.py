from z3 import *
import json

def main():
    cities = ["Paris", "Venice", "Vilnius", "Salzburg", "Amsterdam", "Barcelona", "Hamburg", "Florence", "Tallinn", "Warsaw"]
    city_index = {city: idx for idx, city in enumerate(cities)}
    
    days_arr = [2, 3, 3, 4, 2, 5, 4, 5, 2, 4]
    
    undirected_edges = [
        ("Paris", "Venice"),
        ("Barcelona", "Amsterdam"),
        ("Amsterdam", "Warsaw"),
        ("Amsterdam", "Vilnius"),
        ("Barcelona", "Warsaw"),
        ("Warsaw", "Venice"),
        ("Amsterdam", "Hamburg"),
        ("Barcelona", "Hamburg"),
        ("Barcelona", "Florence"),
        ("Barcelona", "Venice"),
        ("Paris", "Hamburg"),
        ("Paris", "Vilnius"),
        ("Paris", "Amsterdam"),
        ("Paris", "Florence"),
        ("Florence", "Amsterdam"),
        ("Vilnius", "Warsaw"),
        ("Barcelona", "Tallinn"),
        ("Paris", "Warsaw"),
        ("Tallinn", "Warsaw"),
        ("Amsterdam", "Tallinn"),
        ("Paris", "Tallinn"),
        ("Paris", "Barcelona"),
        ("Venice", "Hamburg"),
        ("Warsaw", "Hamburg"),
        ("Hamburg", "Salzburg"),
        ("Amsterdam", "Venice")
    ]
    directed_edges = set()
    for a, b in undirected_edges:
        directed_edges.add((a, b))
        directed_edges.add((b, a))
    directed_edges.add(("Tallinn", "Vilnius"))
    
    directed_edges_index = set()
    for a, b in directed_edges:
        i = city_index[a]
        j = city_index[b]
        directed_edges_index.add((i, j))
    
    solver = Solver()
    O = [Int(f'O_{i}') for i in range(10)]
    s = [Int(f's_{i}') for i in range(10)]
    
    solver.add(O[0] == city_index["Paris"])
    solver.add(O[1] == city_index["Barcelona"])
    for i in range(10):
        solver.add(O[i] >= 0, O[i] < 10)
    solver.add(Distinct(O))
    
    solver.add(s[0] == 1)
    
    days_func = Function('days_func', IntSort(), IntSort())
    for idx, d in enumerate(days_arr):
        solver.add(days_func(idx) == d)
    
    for i in range(1, 10):
        solver.add(s[i] == s[i-1] + days_func(O[i-1]) - 1)
    
    hamburg_idx = city_index["Hamburg"]
    salzburg_idx = city_index["Salzburg"]
    tallinn_idx = city_index["Tallinn"]
    for i in range(10):
        solver.add(If(O[i] == hamburg_idx, s[i] == 19, True))
        solver.add(If(O[i] == salzburg_idx, s[i] == 22, True))
        solver.add(If(O[i] == tallinn_idx, And(s[i] >= 10, s[i] <= 12), True))
    
    for i in range(9):
        edge_constraints = []
        for (a, b) in directed_edges_index:
            edge_constraints.append(And(O[i] == a, O[i+1] == b))
        solver.add(Or(edge_constraints))
    
    solver.add(s[9] + days_func(O[9]) - 1 == 25)
    
    if solver.check() == sat:
        model = solver.model()
        O_val = [model.evaluate(O[i]).as_long() for i in range(10)]
        s_val = [model.evaluate(s[i]).as_long() for i in range(10)]
        
        itinerary = []
        for i in range(10):
            start = s_val[i]
            duration = days_arr[O_val[i]]
            end = start + duration - 1
            city_name = cities[O_val[i]]
            itinerary.append({"day_range": f"Day {start}-{end}", "place": city_name})
            if i < 9:
                itinerary.append({"day_range": f"Day {end}", "place": city_name})
                next_city = cities[O_val[i+1]]
                itinerary.append({"day_range": f"Day {end}", "place": next_city})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()