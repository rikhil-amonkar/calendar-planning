from z3 import *

def main():
    # City mapping
    Manchester, Stuttgart, Madrid, Vienna = 0, 1, 2, 3
    cities = {Manchester: "Manchester", Stuttgart: "Stuttgart", Madrid: "Madrid", Vienna: "Vienna"}
    n_days = 15
    
    # Allowed direct flights (bidirectional)
    allowed_flights = [
        (Vienna, Stuttgart), (Stuttgart, Vienna),
        (Manchester, Vienna), (Vienna, Manchester),
        (Madrid, Vienna), (Vienna, Madrid),
        (Manchester, Stuttgart), (Stuttgart, Manchester),
        (Manchester, Madrid), (Madrid, Manchester)
    ]
    
    solver = Solver()
    
    # Day variables: start_city[i] and end_city[i] for each day i (0-indexed)
    start_city = [Int(f'start_{i}') for i in range(n_days)]
    end_city = [Int(f'end_{i}') for i in range(n_days)]
    
    # City must be one of the four
    for i in range(n_days):
        solver.add(Or([start_city[i] == c for c in cities.keys()]))
        solver.add(Or([end_city[i] == c for c in cities.keys()]))
    
    # Continuity between days: end of day i is start of day i+1
    for i in range(n_days - 1):
        solver.add(end_city[i] == start_city[i+1])
    
    # Flight constraints: either stay or take allowed flight
    for i in range(n_days):
        stay = (start_city[i] == end_city[i])
        valid_flight = Or([And(start_city[i] == a, end_city[i] == b) for (a, b) in allowed_flights])
        solver.add(Or(stay, valid_flight))
    
    # Total days per city (count if city appears at start or end)
    manchester_days = Sum([If(Or(start_city[i] == Manchester, end_city[i] == Manchester), 1, 0) for i in range(n_days)])
    stuttgart_days = Sum([If(Or(start_city[i] == Stuttgart, end_city[i] == Stuttgart), 1, 0) for i in range(n_days)])
    madrid_days = Sum([If(Or(start_city[i] == Madrid, end_city[i] == Madrid), 1, 0) for i in range(n_days)])
    vienna_days = Sum([If(Or(start_city[i] == Vienna, end_city[i] == Vienna), 1, 0) for i in range(n_days)])
    
    solver.add(manchester_days == 7)
    solver.add(stuttgart_days == 5)
    solver.add(madrid_days == 4)
    solver.add(vienna_days == 2)
    
    # Event constraints
    # At least one full day in Manchester during days 1-7 (indices 0-6)
    full_manchester = [And(start_city[i] == Manchester, end_city[i] == Manchester) for i in range(7)]
    solver.add(Or(full_manchester))
    
    # At least one full day in Stuttgart during days 11-15 (indices 10-14)
    full_stuttgart = [And(start_city[i] == Stuttgart, end_city[i] == Stuttgart) for i in range(10, 15)]
    solver.add(Or(full_stuttgart))
    
    # Exactly 3 travel days (where start != end)
    travel_days = Sum([If(start_city[i] != end_city[i], 1, 0) for i in range(n_days)])
    solver.add(travel_days == 3)
    
    # Solve and print
    if solver.check() == sat:
        model = solver.model()
        schedule = []
        for i in range(n_days):
            s = model.eval(start_city[i]).as_long()
            e = model.eval(end_city[i]).as_long()
            if s == e:
                schedule.append(f"Day {i+1}: {cities[s]}")
            else:
                schedule.append(f"Day {i+1}: {cities[s]} and {cities[e]}")
        for s in schedule:
            print(s)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()