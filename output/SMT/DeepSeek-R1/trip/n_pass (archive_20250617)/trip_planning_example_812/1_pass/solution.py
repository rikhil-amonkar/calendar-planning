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
    
    # Parse direct flights into a set of sorted tuples
    direct_set = set()
    for line in lines:
        words = line.split()
        if words[0] == 'from':
            c1 = words[1]
            c2 = words[3]
        else:
            c1 = words[0]
            c2 = words[2]
        edge = tuple(sorted([c1, c2]))
        direct_set.add(edge)
    valid_pairs = list(direct_set)
    
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
    
    # Total days for each city
    for city in cities_list:
        total = 0
        for day in days_list:
            total += If(in_city[day][city], 1, 0)
        solver.add(total == total_days_dict[city])
    
    # Flight constraints for each day
    for day in days_list:
        in_day = [in_city[day][city] for city in cities_list]
        total = sum(If(v, 1, 0) for v in in_day)
        flight_condition = Or([And(in_city[day][p0], in_city[day][p1]) for (p0, p1) in valid_pairs])
        solver.add(Or(total == 1, And(total == 2, flight_condition)))
    
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