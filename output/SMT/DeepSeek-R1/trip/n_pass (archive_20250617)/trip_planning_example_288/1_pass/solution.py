from z3 import *

def main():
    # Define city constants
    Manchester = 0
    Stuttgart = 1
    Madrid = 2
    Vienna = 3
    cities = {Manchester: "Manchester", Stuttgart: "Stuttgart", Madrid: "Madrid", Vienna: "Vienna"}
    n_days = 15

    # Allowed direct flight pairs (undirected)
    allowed_pairs = {(Stuttgart, Vienna), (Vienna, Stuttgart),
                    (Manchester, Vienna), (Vienna, Manchester),
                    (Madrid, Vienna), (Vienna, Madrid),
                    (Manchester, Stuttgart), (Stuttgart, Manchester),
                    (Manchester, Madrid), (Madrid, Manchester)}

    # Initialize Z3 solver
    solver = Solver()
    
    # Arrays for start and end cities for each day (index 0 to 14 for days 1 to 15)
    start_city = [Int(f'start_{i+1}') for i in range(n_days)]
    end_city = [Int(f'end_{i+1}') for i in range(n_days)]
    
    # Constraint: each start_city and end_city must be one of the four cities
    for i in range(n_days):
        solver.add(Or([start_city[i] == c for c in cities.keys()]))
        solver.add(Or([end_city[i] == c for c in cities.keys()]))
    
    # Constraint: continuity between consecutive days
    for i in range(1, n_days):
        solver.add(start_city[i] == end_city[i-1])
    
    # Constraint: for each day, either no travel or travel via direct flight
    for i in range(n_days):
        no_travel = (start_city[i] == end_city[i])
        travel_conditions = []
        for (a, b) in allowed_pairs:
            travel_conditions.append(And(start_city[i] == a, end_city[i] == b))
        solver.add(Or(no_travel, Or(travel_conditions)))
    
    # Constraints for total days in each city
    manchester_total = 0
    stuttgart_total = 0
    madrid_total = 0
    vienna_total = 0
    
    for i in range(n_days):
        manchester_total += If(Or(start_city[i] == Manchester, end_city[i] == Manchester), 1, 0)
        stuttgart_total += If(Or(start_city[i] == Stuttgart, end_city[i] == Stuttgart), 1, 0)
        madrid_total += If(Or(start_city[i] == Madrid, end_city[i] == Madrid), 1, 0)
        vienna_total += If(Or(start_city[i] == Vienna, end_city[i] == Vienna), 1, 0)
    
    solver.add(manchester_total == 7)
    solver.add(stuttgart_total == 5)
    solver.add(madrid_total == 4)
    solver.add(vienna_total == 2)
    
    # Event constraints: wedding in Manchester during days 1-7, workshop in Stuttgart during days 11-15
    wedding_days = []
    for i in range(0, 7):  # Days 1-7 (indices 0 to 6)
        wedding_days.append(Or(start_city[i] == Manchester, end_city[i] == Manchester))
    solver.add(Or(wedding_days))
    
    workshop_days = []
    for i in range(10, 15):  # Days 11-15 (indices 10 to 14)
        workshop_days.append(Or(start_city[i] == Stuttgart, end_city[i] == Stuttgart))
    solver.add(Or(workshop_days))
    
    # Additional constraint: exactly 3 travel days (start != end)
    travel_days = Sum([If(start_city[i] != end_city[i], 1, 0) for i in range(n_days)])
    solver.add(travel_days == 3)
    
    # Check for a solution
    if solver.check() == sat:
        model = solver.model()
        # Print the schedule
        for day in range(1, n_days+1):
            idx = day - 1
            start_val = model[start_city[idx]].as_long()
            end_val = model[end_city[idx]].as_long()
            start_city_name = cities[start_val]
            end_city_name = cities[end_val]
            if start_val == end_val:
                print(f"Day {day}: {start_city_name}")
            else:
                print(f"Day {day}: {start_city_name} and {end_city_name}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()