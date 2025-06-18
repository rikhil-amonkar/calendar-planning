import z3

def main():
    # Initialize the solver
    solver = z3.Solver()
    
    # Days and cities
    days = list(range(1, 19))  # Days 1 to 18
    cities = [0, 1, 2, 3, 4, 5]  # 0: Bucharest, 1: Munich, 2: Seville, 3: Stockholm, 4: Tallinn, 5: Milan
    city_names = {
        0: "Bucharest",
        1: "Munich",
        2: "Seville",
        3: "Stockholm",
        4: "Tallinn",
        5: "Milan"
    }
    
    # Variables: in_city[d, i] is True if traveler is in city i on day d
    in_city = {}
    for d in days:
        for i in cities:
            in_city[d, i] = z3.Bool(f"in_{d}_{i}")
    
    # Direct flights (undirected)
    direct_flights = [(0,1), (1,2), (1,3), (1,4), (1,5), (2,5), (3,4), (3,5)]
    allowed_pairs = set()
    for i, j in direct_flights:
        allowed_pairs.add((i, j))
        allowed_pairs.add((j, i))
    
    # Constraints
    # 1. Each day: at least one city, and if two cities, they must be connected by a direct flight
    for d in days:
        # At least one city per day
        solver.add(z3.Or([in_city[d, i] for i in cities]))
        # If two cities, they must be connected
        for i in range(6):
            for j in range(i+1, 6):
                if (i, j) not in allowed_pairs:
                    solver.add(z3.Not(z3.And(in_city[d, i], in_city[d, j])))
    
    # 2. Consecutive days must share at least one city
    for d in range(1, 18):
        common_cities = []
        for i in cities:
            common_cities.append(z3.And(in_city[d, i], in_city[d+1, i]))
        solver.add(z3.Or(common_cities))
    
    # 3. Total days per city
    total_days = [4, 5, 5, 5, 2, 2]  # Bucharest, Munich, Seville, Stockholm, Tallinn, Milan
    for i in cities:
        solver.add(z3.Sum([z3.If(in_city[d, i], 1, 0) for d in days]) == total_days[i])
    
    # 4. Event constraints
    # Bucharest: at least one day between 1-4 and one exclusive day in 1-4
    solver.add(z3.Or([in_city[d, 0] for d in [1,2,3,4]]))  # At least one day in 1-4
    exclusive_bucharest = []
    for d in [1,2,3,4]:
        other_cities = [in_city[d, j] for j in cities if j != 0]
        exclusive_bucharest.append(z3.And(in_city[d, 0], z3.Not(z3.Or(other_cities))))
    solver.add(z3.Or(exclusive_bucharest))  # At least one exclusive day in 1-4
    
    # Munich: at least one day between 4-8 and one exclusive day in 4-8
    solver.add(z3.Or([in_city[d, 1] for d in [4,5,6,7,8]]))  # At least one day in 4-8
    exclusive_munich = []
    for d in [4,5,6,7,8]:
        other_cities = [in_city[d, j] for j in cities if j != 1]
        exclusive_munich.append(z3.And(in_city[d, 1], z3.Not(z3.Or(other_cities))))
    solver.add(z3.Or(exclusive_munich))  # At least one exclusive day in 4-8
    
    # Seville: at least one day between 8-12 and one exclusive day in 8-12
    solver.add(z3.Or([in_city[d, 2] for d in [8,9,10,11,12]]))  # At least one day in 8-12
    exclusive_seville = []
    for d in [8,9,10,11,12]:
        other_cities = [in_city[d, j] for j in cities if j != 2]
        exclusive_seville.append(z3.And(in_city[d, 2], z3.Not(z3.Or(other_cities))))
    solver.add(z3.Or(exclusive_seville))  # At least one exclusive day in 8-12
    
    # 5. Start in Bucharest on day 1
    solver.add(in_city[1, 0])
    solver.add(z3.Not(z3.Or([in_city[1, j] for j in cities if j != 0])))
    
    # 6. End in Tallinn on day 18
    solver.add(in_city[18, 4])
    solver.add(z3.Not(z3.Or([in_city[18, j] for j in cities if j != 4])))
    
    # Additional constraints to enforce specific exclusive days
    # Exclusive Bucharest on day 1 (already enforced by start constraint)
    # Exclusive Munich on day 5
    solver.add(z3.And(in_city[5, 1], z3.Not(z3.Or([in_city[5, j] for j in cities if j != 1]))))
    # Exclusive Seville on day 9
    solver.add(z3.And(in_city[9, 2], z3.Not(z3.Or([in_city[9, j] for j in cities if j != 2]))))
    
    # Solve and print
    if solver.check() == z3.sat:
        model = solver.model()
        schedule = {d: [] for d in days}
        for d in days:
            for i in cities:
                if z3.is_true(model.eval(in_city[d, i])):
                    schedule[d].append(city_names[i])
        for d in days:
            print(f"Day {d}: {', '.join(schedule[d])}")
        
        # Print total days per city
        print("\nTotal days per city:")
        for i in cities:
            count = sum(1 for d in days if z3.is_true(model.eval(in_city[d, i])))
            print(f"{city_names[i]}: {count} days")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()