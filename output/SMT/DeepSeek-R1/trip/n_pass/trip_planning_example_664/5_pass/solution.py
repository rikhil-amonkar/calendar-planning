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
    
    in_city = {}
    for d in days:
        for i in cities:
            in_city[(d, i)] = z3.Bool(f"in_{d}_{i}")
    
    direct_flights = [(0,1), (1,2), (1,3), (1,4), (1,5), (2,5), (3,4), (3,5)]
    allowed_pairs = set()
    for i, j in direct_flights:
        allowed_pairs.add((i, j))
        allowed_pairs.add((j, i))
    
    # Constraint 1: At least one city per day and valid connections
    for d in days:
        solver.add(z3.Or([in_city[(d, i)] for i in cities]))
        for i in range(6):
            for j in range(i+1, 6):
                if (i, j) not in allowed_pairs:
                    solver.add(z3.Not(z3.And(in_city[(d, i)], in_city[(d, j)]))
    
    # Constraint 2: Consecutive days share at least one city
    for d in range(1, 18):
        common = []
        for i in cities:
            common.append(z3.And(in_city[(d, i)], in_city[(d+1, i)]))
        solver.add(z3.Or(common))
    
    # Constraint 3: Total days per city
    total_days = [4, 5, 5, 5, 2, 2]
    for i in cities:
        solver.add(z3.Sum([z3.If(in_city[(d, i)], 1, 0) for d in days]) == total_days[i])
    
    # Constraint 4: Event windows and exclusive days
    # Bucharest: days 1-4
    solver.add(z3.Or([in_city[(d, 0)] for d in [1,2,3,4]]))
    exclusive_bucharest = []
    for d in [1,2,3,4]:
        others = [in_city[(d, j)] for j in cities if j != 0]
        exclusive_bucharest.append(z3.And(in_city[(d, 0)], z3.Not(z3.Or(others))))
    solver.add(z3.Or(exclusive_bucharest))
    
    # Munich: days 4-8
    solver.add(z3.Or([in_city[(d, 1)] for d in [4,5,6,7,8]]))
    exclusive_munich = []
    for d in [4,5,6,7,8]:
        others = [in_city[(d, j)] for j in cities if j != 1]
        exclusive_munich.append(z3.And(in_city[(d, 1)], z3.Not(z3.Or(others))))
    solver.add(z3.Or(exclusive_munich))
    
    # Seville: days 8-12
    solver.add(z3.Or([in_city[(d, 2)] for d in [8,9,10,11,12]]))
    exclusive_seville = []
    for d in [8,9,10,11,12]:
        others = [in_city[(d, j)] for j in cities if j != 2]
        exclusive_seville.append(z3.And(in_city[(d, 2)], z3.Not(z3.Or(others))))
    solver.add(z3.Or(exclusive_seville))
    
    # Constraint 5: Start and end conditions
    solver.add(in_city[(1, 0)])
    solver.add(z3.Not(z3.Or([in_city[(1, j)] for j in cities if j != 0])))
    solver.add(in_city[(18, 4)])
    solver.add(z3.Not(z3.Or([in_city[(18, j)] for j in cities if j != 4])))
    
    # Solve and print
    if solver.check() == z3.sat:
        model = solver.model()
        schedule = {d: [] for d in days}
        for d in days:
            for i in cities:
                if z3.is_true(model.eval(in_city[(d, i)])):
                    schedule[d].append(city_names[i])
        
        for d in days:
            print(f"Day {d}: {', '.join(schedule[d])}")
        
        print("\nTotal days per city:")
        counts = {name: 0 for name in city_names.values()}
        for d in days:
            for city in schedule[d]:
                counts[city] += 1
        for city, count in counts.items():
            print(f"{city}: {count} days")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()