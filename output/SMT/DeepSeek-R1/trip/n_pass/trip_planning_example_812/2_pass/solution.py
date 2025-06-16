from z3 import *

def main():
    # Total days
    days_total = 20
    days_list = list(range(1, days_total + 1))
    cities_list = ['Paris', 'Florence', 'Vienna', 'Porto', 'Munich', 'Nice', 'Warsaw']
    
    # Fixed constraints: city -> list of days
    fixed_constraints = {
        'Vienna': [19, 20],
        'Porto': [1, 2, 3],
        'Warsaw': [13, 14, 15]
    }
    
    # Total days required for each city
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
    
    # Build directed_edges set
    directed_edges = set()
    for line in lines:
        if line.startswith("from"):
            parts = line.split()
            A = parts[1]
            B = parts[3]
            directed_edges.add((A, B))
        else:
            parts = line.split()
            A = parts[0]
            B = parts[2]
            directed_edges.add((A, B))
            directed_edges.add((B, A))
    
    # Create Z3 variables: in_city[day][city]
    in_city = {}
    for day in days_list:
        in_city[day] = {}
        for city in cities_list:
            in_city[day][city] = Bool(f"day{day}_{city}")
    
    # Initialize solver
    solver = Solver()
    
    # Fixed constraints for Vienna, Porto, Warsaw
    for city, fixed_days in fixed_constraints.items():
        for day in days_list:
            if day in fixed_days:
                solver.add(in_city[day][city] == True)
            else:
                solver.add(in_city[day][city] == False)
    
    # Day 1: only Porto
    for city in cities_list:
        if city != 'Porto':
            solver.add(in_city[1][city] == False)
        else:
            solver.add(in_city[1][city] == True)
    
    # Day 20: only Vienna
    for city in cities_list:
        if city != 'Vienna':
            solver.add(in_city[20][city] == False)
        else:
            solver.add(in_city[20][city] == True)
    
    # Total days for each city
    for city in cities_list:
        total = 0
        for day in days_list:
            total += If(in_city[day][city], 1, 0)
        solver.add(total == total_days_dict[city])
    
    # For each day, the traveler is in 1 or 2 cities
    for day in days_list:
        in_day = [in_city[day][city] for city in cities_list]
        total = Sum([If(v, 1, 0) for v in in_day])
        solver.add(Or(total == 1, total == 2))
    
    # Flight constraints for travel days (days with two cities) for d>=2
    for d in range(2, days_total + 1):
        for A in cities_list:
            for B in cities_list:
                if A >= B:
                    continue
                # Check if the traveler is in exactly A and B on day d
                two_cities = And(in_city[d][A], in_city[d][B], 
                                 Sum([If(in_city[d][C], 1, 0) for C in cities_list]) == 2)
                
                # They must have been in exactly one of A or B on day d-1
                in_A_prev = in_city[d-1][A]
                in_B_prev = in_city[d-1][B]
                exactly_one_prev = Or(
                    And(in_A_prev, Not(in_B_prev)),
                    And(in_B_prev, Not(in_A_prev))
                )
                solver.add(Implies(two_cities, exactly_one_prev))
                
                # Flight direction constraint
                flight_constraint = Or(
                    And(And(in_A_prev, Not(in_B_prev)), (A, B) in directed_edges),
                    And(And(in_B_prev, Not(in_A_prev)), (B, A) in directed_edges)
                )
                solver.add(Implies(two_cities, flight_constraint))
    
    # Continuity constraint: consecutive days must share at least one city
    for day in range(1, days_total):
        common_cities = []
        for city in cities_list:
            common_cities.append(And(in_city[day][city], in_city[day + 1][city]))
        solver.add(Or(common_cities))
    
    # Check for a solution
    if solver.check() == sat:
        model = solver.model()
        # Print the schedule
        print("Schedule:")
        for day in days_list:
            cities_on_day = []
            for city in cities_list:
                if is_true(model.eval(in_city[day][city])):
                    cities_on_day.append(city)
            print(f"Day {day}: {', '.join(cities_on_day)}")
    else:
        print("No solution found")

if __name__ == '__main__':
    main()