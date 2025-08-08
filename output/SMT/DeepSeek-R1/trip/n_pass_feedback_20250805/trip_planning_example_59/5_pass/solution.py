from z3 import Solver, Int, Or, And, If, Sum, sat
import json

def main():
    cities = {0: "Bucharest", 1: "Lyon", 2: "Porto"}
    n_days = 16
    s = Solver()
    
    M = [Int(f'M_{i+1}') for i in range(n_days)]
    E = [Int(f'E_{i+1}') for i in range(n_days)]
    
    # Each M[i] and E[i] must be 0, 1, or 2
    for i in range(n_days):
        s.add(Or(M[i] == 0, M[i] == 1, M[i] == 2))
        s.add(Or(E[i] == 0, E[i] == 1, E[i] == 2))
    
    # Evening of day i must match morning of day i+1
    for i in range(n_days - 1):
        s.add(E[i] == M[i+1])
    
    # Valid flights: Bucharest<->Lyon and Lyon<->Porto
    valid_flights = [(0, 1), (1, 0), (1, 2), (2, 1)]
    for i in range(n_days):
        s.add(Or(
            M[i] == E[i],  # Stay in the same city
            Or([And(M[i] == a, E[i] == b) for (a, b) in valid_flights])  # Valid flight
        ))
    
    # Count days in each city (a day counts if traveler is in city at morning or evening)
    b_days = Sum([If(Or(M[i] == 0, E[i] == 0), 1, 0) for i in range(n_days)])
    l_days = Sum([If(Or(M[i] == 1, E[i] == 1), 1, 0) for i in range(n_days)])
    p_days = Sum([If(Or(M[i] == 2, E[i] == 2), 1, 0) for i in range(n_days)])
    
    s.add(b_days == 7)
    s.add(l_days == 7)
    s.add(p_days == 4)
    
    # Wedding in Bucharest within first 7 days
    s.add(Or([Or(M[i] == 0, E[i] == 0) for i in range(7)]))
    
    if s.check() == sat:
        model = s.model()
        M_vals = [model.evaluate(M[i]).as_long() for i in range(n_days)]
        
        # Aggregate consecutive days with same morning city into segments
        segments = []
        start_day = 1
        current_city = M_vals[0]
        for day in range(1, n_days):
            if M_vals[day] != current_city:
                segments.append({
                    "day_range": f"Day {start_day}-{day}",
                    "place": cities[current_city]
                })
                start_day = day + 1
                current_city = M_vals[day]
        segments.append({
            "day_range": f"Day {start_day}-{n_days}",
            "place": cities[current_city]
        })
        
        result = {"itinerary": segments}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()