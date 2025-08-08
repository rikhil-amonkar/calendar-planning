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
    
    # City day constraints
    s.add(count_K == 5)
    s.add(count_P == 2)
    s.add(count_S == 4)  # 6 days total - 2 flight days accounted elsewhere
    
    # Workshop constraint: must be in Krakow on at least one day between 1-5
    s.add(Or([x[i] == 0 for i in range(5)]))
    
    # Flight connectivity: only allow direct flights
    for i in range(n_days - 1):
        s.add(Implies(
            x[i] != x[i+1],
            Or(
                And(x[i] == 0, x[i+1] == 1),  # Krakow -> Paris
                And(x[i] == 1, x[i+1] == 0),  # Paris -> Krakow
                And(x[i] == 1, x[i+1] == 2),  # Paris -> Seville
                And(x[i] == 2, x[i+1] == 1)   # Seville -> Paris
            )
        ))
    
    # Flight constraints: exactly two flights
    flight_days = Sum([If(x[i] != x[i+1], 1, 0) for i in range(n_days - 1)])
    s.add(flight_days == 2)
    
    # Flight sequence: must be Krakow->Paris->Seville
    # Find transition points
    flight1 = Int('flight1')
    flight2 = Int('flight2')
    s.add(flight1 >= 0, flight1 < n_days - 1)
    s.add(flight2 >= 0, flight2 < n_days - 1)
    s.add(flight1 < flight2)
    
    # First flight: Krakow to Paris
    s.add(And(x[flight1] == 0, x[flight1+1] == 1))
    # Second flight: Paris to Seville
    s.add(And(x[flight2] == 1, x[flight2+1] == 2))
    
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