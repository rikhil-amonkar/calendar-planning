from z3 import *

def main():
    # City mapping
    Manchester, Stuttgart, Madrid, Vienna = 0, 1, 2, 3
    cities = {
        Manchester: "Manchester",
        Stuttgart: "Stuttgart",
        Madrid: "Madrid",
        Vienna: "Vienna"
    }
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
    
    # Arrays for start and end cities each day (0-indexed days 0-14)
    start_city = [Int(f'start_{i}') for i in range(n_days)]
    end_city = [Int(f'end_{i}') for i in range(n_days)]
    
    # Ensure valid city assignments
    for i in range(n_days):
        solver.add(Or([start_city[i] == c for c in cities.keys()]))
        solver.add(Or([end_city[i] == c for c in cities.keys()]))
    
    # Continuity constraint: end of day i is start of day i+1
    for i in range(n_days - 1):
        solver.add(end_city[i] == start_city[i+1])
    
    # Flight constraints: either stay or take allowed flight
    for i in range(n_days):
        stay = (start_city[i] == end_city[i])
        valid_flights = Or([And(start_city[i] == a, end_city[i] == b) for (a, b) in allowed_flights])
        solver.add(Or(stay, valid_flights))
    
    # Total days per city (count city if appears at start or end)
    manchester_days = Sum([If(Or(start_city[i] == Manchester, end_city[i] == Manchester), 1, 0) for i in range(n_days)])
    stuttgart_days = Sum([If(Or(start_city[i] == Stuttgart, end_city[i] == Stuttgart), 1, 0) for i in range(n_days)])
    madrid_days = Sum([If(Or(start_city[i] == Madrid, end_city[i] == Madrid), 1, 0) for i in range(n_days)])
    vienna_days = Sum([If(Or(start_city[i] == Vienna, end_city[i] == Vienna), 1, 0) for i in range(n_days)])
    
    solver.add(manchester_days == 7)
    solver.add(stuttgart_days == 5)
    solver.add(madrid_days == 4)
    solver.add(vienna_days == 2)
    
    # Event constraints: require at least one FULL day in each event period
    wedding_days = [And(start_city[i] == Manchester, end_city[i] == Manchester) for i in range(7)]  # Days 1-7
    workshop_days = [And(start_city[i] == Stuttgart, end_city[i] == Stuttgart) for i in range(10, 15)]  # Days 11-15
    solver.add(Or(wedding_days))
    solver.add(Or(workshop_days))
    
    # Exactly 3 travel days (where start != end)
    travel_days = Sum([If(start_city[i] != end_city[i], 1, 0) for i in range(n_days)])
    solver.add(travel_days == 3)
    
    # Solve and print
    if solver.check() == sat:
        model = solver.model()
        for i in range(n_days):
            s = model.eval(start_city[i]).as_long()
            e = model.eval(end_city[i]).as_long()
            if s == e:
                print(f"Day {i+1}: {cities[s]}")
            else:
                print(f"Day {i+1}: {cities[s]} and {cities[e]}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()