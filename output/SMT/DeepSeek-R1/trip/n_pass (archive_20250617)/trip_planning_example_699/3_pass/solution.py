from z3 import *

def main():
    days = 16
    cities = 6
    city_names = {
        0: "Dublin",
        1: "Hamburg",
        2: "Helsinki",
        3: "London",
        4: "Mykonos",
        5: "Reykjavik"
    }
    
    allowed_edges = [
        (0, 1), (0, 2), (0, 3), (0, 5),
        (1, 2), (1, 3),
        (2, 3), (2, 5),
        (3, 4), (3, 5)
    ]
    allowed_set = set(allowed_edges)
    
    in_d_c = [[Bool(f"in_{d}_{c}") for c in range(cities)] for d in range(days)]
    
    s = Solver()
    
    # Fixed constraints per day
    # Day 1: only Hamburg
    s.add(in_d_c[0][1] == True)
    for c in [0, 2, 3, 4, 5]:
        s.add(in_d_c[0][c] == False)
    
    # Day 2: Hamburg and Dublin
    s.add(in_d_c[1][0] == True)
    s.add(in_d_c[1][1] == True)
    for c in [2, 3, 4, 5]:
        s.add(in_d_c[1][c] == False)
    
    # Days 3, 4, 5: only Dublin
    for d in [2, 3, 4]:  # indices for days 3, 4, 5
        s.add(in_d_c[d][0] == True)
        for c in [1, 2, 3, 4, 5]:
            s.add(in_d_c[d][c] == False)
    
    # Day 6: Dublin and one other city (they leave Dublin on day 6)
    s.add(in_d_c[5][0] == True)
    # They are in exactly one more city on day 6
    other_city = Or(in_d_c[5][2], in_d_c[5][3], in_d_c[5][5])
    s.add(other_city)
    for c in [1, 4]:
        s.add(in_d_c[5][c] == False)
    
    # Days 9 and 10: exclusively in Reykjavik
    for d in [8, 9]:  # days 9 and 10 (0-indexed)
        s.add(in_d_c[d][5] == True)
        for c in [0, 1, 2, 3, 4]:
            s.add(in_d_c[d][c] == False)
    
    # Mykonos: 3 days starting on day 14
    s.add(in_d_c[13][4] == True)  # Day 14
    s.add(in_d_c[14][4] == True)  # Day 15
    s.add(in_d_c[15][4] == True)  # Day 16
    
    # Not in Dublin after day 6
    for d in range(6, days):
        s.add(in_d_c[d][0] == False)
    
    # Not in Hamburg after day 2
    for d in range(2, days):
        s.add(in_d_c[d][1] == False)
    
    # Total days per city
    total_dublin = Sum([If(in_d_c[d][0], 1, 0) for d in range(days)])
    s.add(total_dublin == 5)
    
    total_hamburg = Sum([If(in_d_c[d][1], 1, 0) for d in range(days)])
    s.add(total_hamburg == 2)
    
    total_helsinki = Sum([If(in_d_c[d][2], 1, 0) for d in range(days)])
    s.add(total_helsinki == 4)
    
    total_london = Sum([If(in_d_c[d][3], 1, 0) for d in range(days)])
    s.add(total_london == 5)
    
    total_mykonos = Sum([If(in_d_c[d][4], 1, 0) for d in range(days)])
    s.add(total_mykonos == 3)
    
    # Each day in 1 or 2 cities
    for d in range(days):
        total_cities = Sum([If(in_d_c[d][c], 1, 0) for c in range(cities)])
        s.add(Or(total_cities == 1, total_cities == 2))
    
    # Allowed flights: if two cities on the same day, must be connected
    for d in range(days):
        for i in range(cities):
            for j in range(i+1, cities):
                if (i, j) not in allowed_set and (j, i) not in allowed_set:
                    s.add(Not(And(in_d_c[d][i], in_d_c[d][j])))
    
    # Consecutive days share at least one city
    for d in range(days - 1):
        s.add(Or([And(in_d_c[d][c], in_d_c[d+1][c]) for c in range(cities)]))
    
    if s.check() == sat:
        m = s.model()
        schedule = []
        for d in range(days):
            cities_today = []
            for c in range(cities):
                if is_true(m.evaluate(in_d_c[d][c])):
                    cities_today.append(city_names[c])
            schedule.append(cities_today)
        
        for d in range(days):
            print(f"Day {d+1}: {', '.join(schedule[d])}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()