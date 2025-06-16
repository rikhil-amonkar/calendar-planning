from z3 import *

def main():
    days_total = 20
    days_list = list(range(1, days_total + 1))
    cities_list = ['Paris', 'Florence', 'Vienna', 'Porto', 'Munich', 'Nice', 'Warsaw']
    
    # Build directed flight graph
    directed_edges = set()
    connections = [
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
    
    for conn in connections:
        parts = conn.split()
        if parts[0] == "from":
            directed_edges.add((parts[1], parts[3]))
        else:
            directed_edges.add((parts[0], parts[2]))
            directed_edges.add((parts[2], parts[0]))
    
    fixed_days = {
        'Porto': [1, 2, 3],
        'Warsaw': [13, 14, 15],
        'Vienna': [19, 20]
    }
    
    total_days = {
        'Paris': 5,
        'Florence': 3,
        'Vienna': 2,
        'Porto': 3,
        'Munich': 5,
        'Nice': 5,
        'Warsaw': 3
    }
    
    # Create Z3 variables
    in_city = {}
    for day in days_list:
        in_city[day] = {}
        for city in cities_list:
            in_city[day][city] = Bool(f"day{day}_{city}")
    
    solver = Solver()
    
    # Fixed constraints
    for city, days in fixed_days.items():
        for day in days_list:
            if day in days:
                solver.add(in_city[day][city] == True)
            else:
                solver.add(in_city[day][city] == False)
    
    # Day 1 must be only Porto
    solver.add(in_city[1]['Porto'] == True)
    for city in cities_list:
        if city != 'Porto':
            solver.add(in_city[1][city] == False)
    
    # Day 20 must be only Vienna
    solver.add(in_city[20]['Vienna'] == True)
    for city in cities_list:
        if city != 'Vienna':
            solver.add(in_city[20][city] == False)
    
    # Total days per city
    for city, count in total_days.items():
        solver.add(Sum([If(in_city[day][city], 1, 0) for day in days_list]) == count)
    
    # 1-2 cities per day
    for day in days_list:
        cities_present = [in_city[day][city] for city in cities_list]
        solver.add(Or(
            Sum([If(c, 1, 0) for c in cities_present]) == 1,
            Sum([If(c, 1, 0) for c in cities_present]) == 2
        ))
    
    # Consecutive days share at least one city
    for d in range(1, days_total):
        solver.add(Or([And(in_city[d][city], in_city[d+1][city]) for city in cities_list]))
    
    # Travel day constraints
    for d in range(2, days_total + 1):
        for city1 in cities_list:
            for city2 in cities_list:
                if city1 == city2:
                    continue
                    
                # Check if day d has exactly these two cities
                other_cities = [c for c in cities_list if c not in (city1, city2)]
                exactly_two = And(
                    in_city[d][city1],
                    in_city[d][city2],
                    *[Not(in_city[d][c]) for c in other_cities]
                )
                
                # Shared cities with previous day
                shared1 = And(in_city[d-1][city1], in_city[d][city1])
                shared2 = And(in_city[d-1][city2], in_city[d][city2])
                
                # Exactly one shared city
                solver.add(Implies(exactly_two, Or(shared1, shared2)))
                solver.add(Implies(exactly_two, Not(And(shared1, shared2))))
                
                # Valid flight transition
                if (city1, city2) in directed_edges or (city2, city1) in directed_edges:
                    flight_options = []
                    if (city1, city2) in directed_edges:
                        flight_options.append(shared1)
                    if (city2, city1) in directed_edges:
                        flight_options.append(shared2)
                    solver.add(Implies(exactly_two, Or(flight_options)))
                else:
                    solver.add(Not(exactly_two))
    
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