from z3 import *
import json

def main():
    s = Solver()
    n_days = 11
    city_names = {0: "Krakow", 1: "Paris", 2: "Seville"}
    
    # Decision variables: for each day, which city (0, 1, or 2)
    x = [Int(f'x_{i}') for i in range(n_days)]
    for i in range(n_days):
        s.add(Or(x[i] == 0, x[i] == 1, x[i] == 2))
    
    # Start in Krakow (day 1)
    s.add(x[0] == 0)
    
    # Count days in each city
    count_K = Sum([If(x[i] == 0, 1, 0) for i in range(n_days)])
    count_P = Sum([If(x[i] == 1, 1, 0) for i in range(n_days)])
    count_S = Sum([If(x[i] == 2, 1, 0) for i in range(n_days)])
    
    # Define arrival in Paris (flight from Krakow to Paris)
    arrival_P_conditions = []
    for i in range(n_days - 1):
        arrival_P_conditions.append(And(x[i] == 0, x[i+1] == 1))
    arrival_P = Int('arrival_P')
    s.add(arrival_P == If(Or(arrival_P_conditions), 1, 0))
    
    # Define arrival in Seville (flight from Paris to Seville)
    arrival_S_conditions = []
    for i in range(n_days - 1):
        arrival_S_conditions.append(And(x[i] == 1, x[i+1] == 2))
    arrival_S = Int('arrival_S')
    s.add(arrival_S == If(Or(arrival_S_conditions), 1, 0))
    
    # City day constraints with arrival accounting
    s.add(count_K == 5)
    s.add(count_P + arrival_P == 2)
    s.add(count_S + arrival_S == 6)
    
    # Workshop constraint: must be in Krakow on at least one day between 1-5
    s.add(Or([x[i] == 0 for i in range(5)]))
    
    # Flight connectivity: only direct flights allowed
    for i in range(n_days - 1):
        s.add(Implies(
            x[i] != x[i+1],
            Or(
                And(x[i] == 0, x[i+1] == 1),
                And(x[i] == 1, x[i+1] == 0),
                And(x[i] == 1, x[i+1] == 2),
                And(x[i] == 2, x[i+1] == 1)
            )
        ))
    
    # Exactly two flights
    s.add(arrival_P + arrival_S == 2)
    
    # Solve and output
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(n_days):
            city_index = m[x[i]].as_long()
            itinerary.append({"day": i+1, "place": city_names[city_index]})
        print(json.dumps({"itinerary": itinerary}))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()