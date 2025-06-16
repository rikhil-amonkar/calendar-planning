from z3 import *

def main():
    # Total days and cities
    days = 16
    cities = 6
    # City indices: 0=Dublin, 1=Hamburg, 2=Helsinki, 3=London, 4=Mykonos, 5=Reykjavik
    city_names = {
        0: "Dublin",
        1: "Hamburg",
        2: "Helsinki",
        3: "London",
        4: "Mykonos",
        5: "Reykjavik"
    }
    
    # Allowed direct flights as tuples (min_city, max_city)
    allowed_edges = [
        (0, 1), (0, 2), (0, 3), (0, 5),
        (1, 2), (1, 3),
        (2, 3), (2, 5),
        (3, 4), (3, 5)
    ]
    allowed_set = set(allowed_edges)
    
    # Create a 2D list of Z3 boolean variables: in_d_c[d][c] for day d (0-15) and city c (0-5)
    in_d_c = [[Bool(f"in_{d+1}_{c}") for c in range(cities)] for d in range(days)]
    
    s = Solver()
    
    # Fixed constraints per day and city
    # Day 1: only in Hamburg (city 1)
    s.add(in_d_c[0][1] == True)
    for c in [0, 2, 3, 4, 5]:
        s.add(in_d_c[0][c] == False)
    
    # Day 2: in Hamburg (1) and Dublin (0)
    s.add(in_d_c[1][0] == True)
    s.add(in_d_c[1][1] == True)
    for c in [2, 3, 4, 5]:
        s.add(in_d_c[1][c] == False)
    
    # Days 3-6: must be in Dublin (0)
    for d in [2, 3, 4, 5]:  # indices for days 3 to 6
        s.add(in_d_c[d][0] == True)
    
    # For days 7-16: not in Dublin (0)
    for d in range(6, 16):   # indices for days 7 to 16
        s.add(in_d_c[d][0] == False)
    
    # For Hamburg (1): only in days 1 and 2, so days 3-16: not in Hamburg
    for d in range(2, 16):   # indices for days 3 to 16
        s.add(in_d_c[d][1] == False)
    
    # For Reykjavik (5): must be exclusively in Reykjavik on days 9 and 10 (indices 8 and 9)
    s.add(in_d_c[8][5] == True)  # Day 9: Reykjavik
    s.add(in_d_c[9][5] == True)  # Day 10: Reykjavik
    # On days 9 and 10, no other cities
    for d in [8, 9]:
        for c in [0, 1, 2, 3, 4]:
            s.add(in_d_c[d][c] == False)
    
    # Total days constraints for other cities
    s.add(Sum([If(in_d_c[d][2], 1, 0) for d in range(16)]) == 4)  # Helsinki: 4 days
    s.add(Sum([If(in_d_c[d][3], 1, 0) for d in range(16)]) == 5)  # London: 5 days
    s.add(Sum([If(in_d_c[d][4], 1, 0) for d in range(16)]) == 3)  # Mykonos: 3 days
    
    # Constraints for each day
    for d in range(16):
        # Each day: in 1 or 2 cities
        total_cities = Sum([If(in_d_c[d][c], 1, 0) for c in range(cities)])
        s.add(Or(total_cities == 1, total_cities == 2))
        
        # For each pair of distinct cities, if both are present, they must be connected by a direct flight
        for i in range(cities):
            for j in range(i+1, cities):
                edge = (i, j)
                if edge not in allowed_set:
                    s.add(Not(And(in_d_c[d][i], in_d_c[d][j])))
    
    # Consecutive days must share at least one city
    for d in range(15):  # from day1 to day15 (0-indexed: 0 to 14)
        s.add(Or([And(in_d_c[d][c], in_d_c[d+1][c]) for c in range(cities)]))
    
    # Solve the problem
    if s.check() == sat:
        m = s.model()
        schedule = []
        for d in range(16):
            cities_today = []
            for c in range(cities):
                if is_true(m.evaluate(in_d_c[d][c])):
                    cities_today.append(city_names[c])
            schedule.append(cities_today)
        
        # Output the schedule
        for d in range(16):
            print(f"Day {d+1}: {', '.join(schedule[d])}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()