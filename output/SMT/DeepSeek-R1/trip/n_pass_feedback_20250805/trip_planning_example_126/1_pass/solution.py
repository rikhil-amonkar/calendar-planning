from z3 import *
import json

def main():
    # Create solver
    s = Solver()
    
    # 11 days, each day assigned to a city: 0=Krakow, 1=Paris, 2=Seville
    x = IntVector('x', 11)
    
    # Each day must be 0, 1, or 2
    for i in range(11):
        s.add(Or(x[i] == 0, x[i] == 1, x[i] == 2))
    
    # Count the days assigned to each city
    count_K = Sum([If(x[i] == 0, 1, 0) for i in range(11)])
    count_P = Sum([If(x[i] == 1, 1, 0) for i in range(11)])
    count_S = Sum([If(x[i] == 2, 1, 0) for i in range(11)])
    
    # Define leave_K: 1 if there's a flight leaving Krakow, else 0
    leave_K = Int('leave_K')
    s.add(leave_K == If(Or([And(x[i-1] == 0, x[i] != 0) for i in range(1, 11)]), 1, 0)
    
    leave_P = Int('leave_P')
    s.add(leave_P == If(Or([And(x[i-1] == 1, x[i] != 1) for i in range(1, 11)]), 1, 0)
    
    leave_S = Int('leave_S')
    s.add(leave_S == If(Or([And(x[i-1] == 2, x[i] != 2) for i in range(1, 11)]), 1, 0)
    
    # Constraints on total days per city
    s.add(count_K + leave_K == 5)
    s.add(count_P + leave_P == 2)
    s.add(count_S + leave_S == 6)
    s.add(leave_K + leave_P + leave_S == 2)  # Exactly two flights (departures)
    
    # Workshop in Krakow between day 1 and 5: must be in Krakow on at least one day in [1,5]
    conditions = []
    for d in range(5):  # Days 1 to 5 (indices 0 to 4)
        if d == 0:
            cond = (x[0] == 0)
        else:
            cond = Or(x[d] == 0, x[d-1] == 0)
        conditions.append(cond)
    s.add(Or(conditions))
    
    # Flight connectivity: changes only between connected cities
    for i in range(1, 11):
        s.add(Implies(
            x[i] != x[i-1],
            Or(
                And(x[i-1] == 0, x[i] == 1),
                And(x[i-1] == 1, x[i] == 0),
                And(x[i-1] == 1, x[i] == 2),
                And(x[i-1] == 2, x[i] == 1)
            )
        ))
    
    # Exactly two changes (flights)
    num_changes = Sum([If(x[i] != x[i-1], 1, 0) for i in range(1, 11)])
    s.add(num_changes == 2)
    
    # Check and get solution
    if s.check() == sat:
        m = s.model()
        itinerary = []
        city_names = {0: "Krakow", 1: "Paris", 2: "Seville"}
        for i in range(11):
            val = m[x[i]].as_long()
            itinerary.append({"day": i+1, "place": city_names[val]})
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()