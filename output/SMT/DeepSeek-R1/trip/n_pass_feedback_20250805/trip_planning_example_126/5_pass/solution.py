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
    
    # Start in Krakow on day 1
    s.add(x[0] == 0)
    
    # Count days in each city
    count_K = Sum([If(x[i] == 0, 1, 0) for i in range(n_days)])
    count_P = Sum([If(x[i] == 1, 1, 0) for i in range(n_days)])
    count_S = Sum([If(x[i] == 2, 1, 0) for i in range(n_days)])
    
    # Flight detection
    flight_0_1 = [If(And(x[i] == 0, x[i+1] == 1), 1, 0) for i in range(n_days-1)]
    flight_1_2 = [If(And(x[i] == 1, x[i+1] == 2), 1, 0) for i in range(n_days-1)]
    
    # Exactly two flights: Krakow->Paris and Paris->Seville
    s.add(Sum(flight_0_1) == 1)
    s.add(Sum(flight_1_2) == 1)
    
    # Flight sequence: Krakow->Paris must come before Paris->Seville
    for i in range(n_days-1):
        for j in range(n_days-1):
            s.add(Implies(
                And(flight_0_1[i] == 1, flight_1_2[j] == 1),
                i < j
            ))
    
    # City day constraints (5 Krakow, 2 Paris, 4 Seville)
    s.add(count_K == 5)
    s.add(count_P == 2)
    s.add(count_S == 4)
    
    # Workshop constraint: must be in Krakow on at least one day between 1-5
    s.add(Or([x[i] == 0 for i in range(5)]))
    
    # Flight connectivity: only direct flights allowed
    for i in range(n_days - 1):
        s.add(Implies(
            x[i] != x[i+1],
            Or(
                And(x[i] == 0, x[i+1] == 1),  # Krakow->Paris
                And(x[i] == 1, x[i+1] == 0),  # Paris->Krakow
                And(x[i] == 1, x[i+1] == 2),  # Paris->Seville
                And(x[i] == 2, x[i+1] == 1)   # Seville->Paris
            )
        ))
    
    # No returns after flights
    for i in range(n_days-1):
        s.add(Implies(
            And(x[i] == 0, x[i+1] == 1),
            And([x[j] != 0 for j in range(i+1, n_days)])
        ))
        s.add(Implies(
            And(x[i] == 1, x[i+1] == 2),
            And([x[j] != 1 for j in range(i+1, n_days)])
        ))
    
    # Solve and output
    if s.check() == sat:
        m = s.model()
        itinerary = []
        current_city = m[x[0]].as_long()
        start_day = 1
        for i in range(1, n_days):
            if m[x[i]].as_long() != current_city:
                itinerary.append({
                    "day_range": f"Day {start_day}-{i}",
                    "place": city_names[current_city]
                })
                current_city = m[x[i]].as_long()
                start_day = i+1
        itinerary.append({
            "day_range": f"Day {start_day}-{n_days}",
            "place": city_names[current_city]
        })
        
        print(json.dumps({"itinerary": itinerary}))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()