from z3 import *

def main():
    # City names and their indices
    cities = ["Paris", "Venice", "Vilnius", "Salzburg", "Amsterdam", "Barcelona", "Hamburg", "Florence", "Tallinn", "Warsaw"]
    city_index = {city: idx for idx, city in enumerate(cities)}
    
    # Days required for each city
    days_arr = [2, 3, 3, 4, 2, 5, 4, 5, 2, 4]  # Corresponding to cities list
    
    # Build directed flight connections
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
    directed_edges.add(("Tallinn", "Vilnius"))  # Directed edge
    
    # Map to indices
    directed_edges_index = set()
    for a, b in directed_edges:
        i = city_index[a]
        j = city_index[b]
        directed_edges_index.add((i, j))
    
    # Z3 variables and solver
    solver = Solver()
    O = [Int(f'O_{i}') for i in range(10)]
    s = [Int(f's_{i}') for i in range(10)]
    
    # Constraints for O: permutation of cities starting with Paris (index0)
    solver.add(O[0] == 0)
    for i in range(10):
        solver.add(O[i] >= 0, O[i] < 10)
    solver.add(Distinct(O))
    
    # Start day for first city is 1
    solver.add(s[0] == 1)
    
    # Function to get days for a city index
    days_func = Function('days_func', IntSort(), IntSort())
    for idx, d in enumerate(days_arr):
        solver.add(days_func(idx) == d)
    
    # Constraints for start days of subsequent cities
    for i in range(1, 10):
        solver.add(s[i] == s[i-1] + days_func(O[i-1]) - 1)
    
    # Specific constraints for cities
    hamburg_idx = city_index["Hamburg"]
    salzburg_idx = city_index["Salzburg"]
    barcelona_idx = city_index["Barcelona"]
    tallinn_idx = city_index["Tallinn"]
    for i in range(10):
        solver.add(If(O[i] == hamburg_idx, s[i] == 19, True))
        solver.add(If(O[i] == salzburg_idx, s[i] == 22, True))
        solver.add(If(O[i] == barcelona_idx, s[i] <= 6, True))
        solver.add(If(O[i] == tallinn_idx, And(s[i] >= 10, s[i] <= 12), True))
    
    # Flight constraints between consecutive cities
    for i in range(9):
        edge_constraints = []
        for (a, b) in directed_edges_index:
            edge_constraints.append(And(O[i] == a, O[i+1] == b))
        solver.add(Or(edge_constraints))
    
    # Final day constraint (should be day 25)
    solver.add(s[9] + days_func(O[9]) - 1 == 25)
    
    # Check and get model
    if solver.check() == sat:
        model = solver.model()
        O_val = [model.evaluate(O[i]).as_long() for i in range(10)]
        s_val = [model.evaluate(s[i]).as_long() for i in range(10)]
        
        # Generate itinerary
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
        
        # Output as JSON
        import json
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()