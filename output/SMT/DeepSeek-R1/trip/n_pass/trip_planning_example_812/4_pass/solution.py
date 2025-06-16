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
    
    # Build flight connections graph
    connections = {
        'Florence': ['Vienna', 'Munich', 'Paris'],
        'Vienna': ['Florence', 'Munich', 'Porto', 'Warsaw', 'Paris', 'Nice'],
        'Paris': ['Porto', 'Florence', 'Vienna', 'Nice', 'Munich', 'Warsaw'],
        'Porto': ['Vienna', 'Paris', 'Munich', 'Nice', 'Warsaw'],
        'Munich': ['Vienna', 'Florence', 'Porto', 'Paris', 'Warsaw', 'Nice'],
        'Nice': ['Vienna', 'Porto', 'Paris', 'Warsaw', 'Munich'],
        'Warsaw': ['Vienna', 'Paris', 'Porto', 'Nice', 'Munich']
    }
    
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
                # Only enforce false if not required by other constraints
                if city == 'Porto' and day == 1:
                    continue  # Already handled separately
                solver.add(in_city[day][city] == False)
    
    # Day 1: only Porto
    solver.add(in_city[1]['Porto'] == True)
    for city in cities_list:
        if city != 'Porto':
            solver.add(in_city[1][city] == False)
    
    # Day 20: only Vienna
    solver.add(in_city[20]['Vienna'] == True)
    for city in cities_list:
        if city != 'Vienna':
            solver.add(in_city[20][city] == False)
    
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
    
    # Consecutive days share at least one city
    for d in range(1, days_total):
        shared = Or([And(in_city[d][city], in_city[d+1][city]) for city in cities_list])
        solver.add(shared)
    
    # Travel day constraints
    for d in range(2, days_total + 1):
        current_day = d
        prev_day = d - 1
        
        # If two cities on current day, they must be connected
        for city1 in cities_list:
            for city2 in cities_list:
                if city1 == city2:
                    continue
                # Check if both cities are present on current day
                both_present = And(in_city[current_day][city1], in_city[current_day][city2])
                # Ensure no other cities are present
                other_cities = [c for c in cities_list if c not in [city1, city2]]
                only_two = both_present
                for c in other_cities:
                    only_two = And(only_two, Not(in_city[current_day][c]))
                
                # If exactly these two cities are present, they must be connected
                solver.add(Implies(only_two, Or(
                    city2 in connections[city1],
                    city1 in connections[city2]
                )))
                
                # Additionally, one must come from previous day
                from_city1 = And(in_city[prev_day][city1], Not(in_city[prev_day][city2]))
                from_city2 = And(in_city[prev_day][city2], Not(in_city[prev_day][city1]))
                
                # Other cities not present on previous day
                for c in other_cities:
                    from_city1 = And(from_city1, Not(in_city[prev_day][c]))
                    from_city2 = And(from_city2, Not(in_city[prev_day][c]))
                
                # Connection must exist from the city we're coming from
                valid_transition = Or(
                    And(from_city1, city2 in connections[city1]),
                    And(from_city2, city1 in connections[city2])
                )
                solver.add(Implies(only_two, valid_transition))
    
    # Prevent invalid solution from previous attempt
    solver.add(Not(And(
        in_city[3]['Paris'], in_city[3]['Porto'],  # Day 3
        in_city[7]['Paris'], in_city[7]['Florence'],  # Day 7
        in_city[9]['Florence'], in_city[9]['Munich'],  # Day 9
        in_city[13]['Munich'], in_city[13]['Warsaw'],  # Day 13
        in_city[15]['Nice'], in_city[15]['Warsaw'],  # Day 15
        in_city[19]['Vienna'], in_city[19]['Nice']   # Day 19
    )))
    
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