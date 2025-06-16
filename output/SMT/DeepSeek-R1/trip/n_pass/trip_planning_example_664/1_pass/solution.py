import z3

def main():
    solver = z3.Solver()
    days = list(range(1, 19))
    cities = [0, 1, 2, 3, 4, 5]
    city_names = {
        0: "Bucharest",
        1: "Munich",
        2: "Seville",
        3: "Stockholm",
        4: "Tallinn",
        5: "Milan"
    }
    
    c = {}
    for d in days:
        for i in cities:
            c[(d, i)] = z3.Bool(f"c_{d}_{i}")
    
    edges = set()
    edges.add((0, 1))
    edges.add((1, 2))
    edges.add((1, 3))
    edges.add((1, 4))
    edges.add((1, 5))
    edges.add((2, 5))
    edges.add((3, 4))
    edges.add((3, 5))
    
    for d in days:
        in_cities = [c[(d, i)] for i in cities]
        solver.add(z3.Or(in_cities))
        solver.add(z3.AtMost(*in_cities, 2))
        for i in range(6):
            for j in range(i + 1, 6):
                if (i, j) not in edges and (j, i) not in edges:
                    solver.add(z3.Not(z3.And(c[(d, i)], c[(d, j)])))
    
    for d in range(1, 18):
        common_cities = []
        for i in cities:
            common_cities.append(z3.And(c[(d, i)], c[(d + 1, i)]))
        solver.add(z3.Or(common_cities))
    
    totals = [4, 5, 5, 5, 2, 2]
    for i in cities:
        total_days = z3.Sum([z3.If(c[(d, i)], 1, 0) for d in days])
        solver.add(total_days == totals[i])
    
    bucharest_days = [c[(d, 0)] for d in [1, 2, 3, 4]]
    solver.add(z3.Or(bucharest_days))
    munich_days = [c[(d, 1)] for d in [4, 5, 6, 7, 8]]
    solver.add(z3.Or(munich_days))
    seville_days = [c[(d, 2)] for d in [8, 9, 10, 11, 12]]
    solver.add(z3.Or(seville_days))
    
    if solver.check() == z3.sat:
        model = solver.model()
        schedule = {}
        for d in days:
            schedule[d] = []
            for i in cities:
                if z3.is_true(model.eval(c[(d, i)])):
                    schedule[d].append(city_names[i])
        
        for d in days:
            cities_str = ", ".join(schedule[d])
            print(f"Day {d}: {cities_str}")
        
        print("\nTotal days per city:")
        for i in cities:
            count = 0
            for d in days:
                if z3.is_true(model.eval(c[(d, i)])):
                    count += 1
            print(f"{city_names[i]}: {count} days")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()