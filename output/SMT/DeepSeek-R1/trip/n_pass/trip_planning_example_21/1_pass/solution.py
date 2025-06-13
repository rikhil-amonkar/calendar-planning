from z3 import *

def main():
    n_days = 10
    cities = ['Mykonos', 'Vienna', 'Venice']
    n_cities = len(cities)
    
    # Adjacent city pairs: (Mykonos, Vienna) and (Vienna, Venice)
    adjacent = [(0, 1), (1, 0), (1, 2), (2, 1)]
    
    s = Solver()
    
    # in_city[i][c]: True if on day i we are in city c
    in_city = [[Bool(f"in_{i}_{c}") for c in range(n_cities)] for i in range(n_days)]
    
    # Constraint: Each day must be either in one city or two adjacent cities
    for i in range(n_days):
        # Possibility 1: Exactly one city
        one_city = Or(
            And(in_city[i][0], Not(in_city[i][1]), Not(in_city[i][2])),
            And(in_city[i][1], Not(in_city[i][0]), Not(in_city[i][2])),
            And(in_city[i][2], Not(in_city[i][0]), Not(in_city[i][1]))
        )
        # Possibility 2: Two adjacent cities
        two_cities = Or(
            And(in_city[i][0], in_city[i][1], Not(in_city[i][2])),  # Mykonos and Vienna
            And(in_city[i][1], in_city[i][2], Not(in_city[i][0]))   # Vienna and Venice
        )
        s.add(Or(one_city, two_cities))
    
    # Count travel days (days with two cities)
    travel_days = []
    for i in range(n_days):
        is_travel = Or(
            And(in_city[i][0], in_city[i][1], Not(in_city[i][2])),
            And(in_city[i][1], in_city[i][2], Not(in_city[i][0]))
        )
        travel_days.append(If(is_travel, 1, 0))
    total_travel_days = Sum(travel_days)
    s.add(total_travel_days == 2)
    
    # Total days per city
    total_mykonos = Sum([If(in_city[i][0], 1, 0) for i in range(n_days)])
    total_vienna = Sum([If(in_city[i][1], 1, 0) for i in range(n_days)])
    total_venice = Sum([If(in_city[i][2], 1, 0) for i in range(n_days)])
    s.add(total_mykonos == 2)
    s.add(total_vienna == 4)
    s.add(total_venice == 6)
    
    # Workshop constraint: At least one day in Venice between days 5 and 10 (indices 4 to 9)
    s.add(Or([in_city[i][2] for i in range(4, 10)]))
    
    # Solve and print the schedule
    if s.check() == sat:
        m = s.model()
        schedule = []
        for i in range(n_days):
            current_day = []
            for c in range(n_cities):
                if m.evaluate(in_city[i][c]):
                    current_day.append(cities[c])
            schedule.append(current_day)
        
        for i in range(n_days):
            cities_str = ", ".join(schedule[i])
            print(f"Day {i+1}: {cities_str}")
    else:
        print("No valid schedule found.")

if __name__ == "__main__":
    main()