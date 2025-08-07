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
    
    # Count days in each city
    count_K = Sum([If(x[i] == 0, 1, 0) for i in range(n_days)])
    count_P = Sum([If(x[i] == 1, 1, 0) for i in range(n_days)])
    count_S = Sum([If(x[i] == 2, 1, 0) for i in range(n_days)])
    
    # Define leave_K: 1 if there's at least one transition from Krakow to another city
    conditions_leave_K = []
    for i in range(1, n_days):
        conditions_leave_K.append(And(x[i-1] == 0, x[i] != 0))
    leave_K = Int('leave_K')
    s.add(leave_K == If(Or(conditions_leave_K), 1, 0))
    
    conditions_leave_P = []
    for i in range(1, n_days):
        conditions_leave_P.append(And(x[i-1] == 1, x[i] != 1))
    leave_P = Int('leave_P')
    s.add(leave_P == If(Or(conditions_leave_P), 1, 0))
    
    conditions_leave_S = []
    for i in range(1, n_days):
        conditions_leave_S.append(And(x[i-1] == 2, x[i] != 2))
    leave_S = Int('leave_S')
    s.add(leave_S == If(Or(conditions_leave_S), 1, 0))
    
    # Constraints on total days per city
    s.add(count_K + leave_K == 5)
    s.add(count_P + leave_P == 2)
    s.add(count_S + leave_S == 6)
    s.add(leave_K + leave_P + leave_S == 2)  # Exactly two flights (departures)
    
    # Workshop constraint: must be in Krakow on at least one day between day 1 and day 5 (inclusive)
    workshop_days = [x[i] == 0 for i in range(5)]
    s.add(Or(workshop_days))
    
    # Flight connectivity: only direct flights allowed (Krakow<->Paris, Paris<->Seville)
    for i in range(1, n_days):
        s.add(Implies(
            x[i] != x[i-1],
            Or(
                And(x[i-1] == 0, x[i] == 1),
                And(x[i-1] == 1, x[i] == 0),
                And(x[i-1] == 1, x[i] == 2),
                And(x[i-1] == 2, x[i] == 1)
            )
        ))
    
    # Exactly two changes (flights) in the entire trip
    num_changes = Sum([If(x[i] != x[i-1], 1, 0) for i in range(1, n_days)])
    s.add(num_changes == 2)
    
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