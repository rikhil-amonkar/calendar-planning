from z3 import *

def main():
    days_total = 20
    days_list = list(range(1, days_total + 1))
    cities_list = ['Paris', 'Florence', 'Vienna', 'Porto', 'Munich', 'Nice', 'Warsaw']
    
    fixed_constraints = {
        'Vienna': [19, 20],
        'Porto': [1, 2, 3],
        'Warsaw': [13, 14, 15]
    }
    
    total_days_dict = {
        'Paris': 5,
        'Florence': 3,
        'Vienna': 2,
        'Porto': 3,
        'Munich': 5,
        'Nice': 5,
        'Warsaw': 3
    }
    
    # Direct flights data
    lines = [
        "Florence and Vienna",
        "Paris and Warsaw",
        "Munich and Vienna",
        "Porto and Vienna",
        "Warsaw and Vienna",
        "from Florence to Munich",
        "Munich and Warsaw",
        "Munich and Nice",
        "Paris and Florence",
        "Warsaw and Nice",
        "Porto and Munich",
        "Porto and Nice",
        "Paris and Vienna",
        "Nice and Vienna",
        "Porto and Paris",
        "Paris and Nice",
        "Paris and Munich",
        "Porto and Warsaw"
    ]
    
    directed_edges = set()
    for line in lines:
        if line.startswith("from"):
            parts = line.split()
            directed_edges.add((parts[1], parts[3]))
        else:
            parts = line.split()
            A, B = parts[0], parts[2]
            directed_edges.add((A, B))
            directed_edges.add((B, A))
    
    # Create Z3 variables
    in_city = {}
    for day in days_list:
        in_city[day] = {}
        for city in cities_list:
            in_city[day][city] = Bool(f"day{day}_{city}")
    
    solver = Solver()
    
    # Fixed constraints
    for city, fixed_days in fixed_constraints.items():
        for day in days_list:
            if day in fixed_days:
                solver.add(in_city[day][city] == True)
            else:
                solver.add(in_city[day][city] == False)
    
    # Day 1: only Porto
    for city in cities_list:
        solver.add(in_city[1][city] == (city == 'Porto'))
    
    # Day 20: only Vienna
    for city in cities_list:
        solver.add(in_city[20][city] == (city == 'Vienna'))
    
    # Total days per city
    for city in cities_list:
        total = 0
        for day in days_list:
            total += If(in_city[day][city], 1, 0)
        solver.add(total == total_days_dict[city])
    
    # 1-2 cities per day
    for day in days_list:
        cities_present = [in_city[day][city] for city in cities_list]
        solver.add(Or(
            Sum([If(c, 1, 0) for c in cities_present]) == 1,
            Sum([If(c, 1, 0) for c in cities_present]) == 2
        ))
    
    # Flight constraints for travel days
    for d in range(2, days_total + 1):
        for A in cities_list:
            for B in cities_list:
                if A == B:
                    continue
                # Check if exactly A and B are present on day d
                other_cities = [c for c in cities_list if c not in [A, B]]
                only_A_and_B = And(
                    in_city[d][A],
                    in_city[d][B],
                    *[Not(in_city[d][c]) for c in other_cities]
                )
                
                # On travel day, must come from exactly one of them
                from_A = And(
                    in_city[d-1][A],
                    Not(in_city[d-1][B]),
                    *[Not(in_city[d-1][c]) for c in other_cities],
                    (A, B) in directed_edges
                )
                from_B = And(
                    in_city[d-1][B],
                    Not(in_city[d-1][A]),
                    *[Not(in_city[d-1][c]) for c in other_cities],
                    (B, A) in directed_edges
                )
                
                solver.add(Implies(only_A_and_B, Or(from_A, from_B)))
    
    # Consecutive days share at least one city
    for d in range(1, days_total):
        shared = Or([And(in_city[d][city], in_city[d+1][city]) for city in cities_list])
        solver.add(shared)
    
    # Solve and output
    if solver.check() == sat:
        model = solver.model()
        print("Schedule:")
        for day in days_list:
            present = []
            for city in cities_list:
                if is_true(model.eval(in_city[day][city])):
                    present.append(city)
            print(f"Day {day}: {', '.join(present)}")
    else:
        print("No solution found")

if __name__ == '__main__':
    main()