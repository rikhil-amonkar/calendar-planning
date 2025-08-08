from z3 import *
import json

def main():
    D = 0  # Dubrovnik
    F = 1  # Frankfurt
    K = 2  # Krakow
    cities = {D: "Dubrovnik", F: "Frankfurt", K: "Krakow"}
    
    # State at start of each day (days 1-11)
    s = [Int(f's_{i}') for i in range(11)]
    # Flight on each day (days 1-10)
    flight = [Bool(f'f_{i}') for i in range(10)]
    
    solver = Solver()
    
    # City constraints
    for i in range(11):
        solver.add(Or(s[i] == D, s[i] == F, s[i] == K))
    
    # Start in Dubrovnik
    solver.add(s[0] == D)
    
    # Flight rules
    allowed = [(D, F), (F, D), (F, K), (K, F)]
    for i in range(10):
        no_flight = s[i] == s[i+1]
        with_flight = Or([And(s[i] == a, s[i+1] == b) for a, b in allowed])
        solver.add(flight[i] == with_flight)
        solver.add(Implies(flight[i], with_flight))
        solver.add(Implies(Not(flight[i]), no_flight))
    
    # Presence in cities
    in_city = {c: [Bool(f'in{c}_{i}') for i in range(10)] for c in [D, F, K]}
    for i in range(10):
        solver.add(in_city[D][i] == Or(s[i] == D, And(flight[i], s[i+1] == D)))
        solver.add(in_city[F][i] == Or(s[i] == F, And(flight[i], s[i+1] == F)))
        solver.add(in_city[K][i] == Or(s[i] == K, And(flight[i], s[i+1] == K)))
    
    # Total days per city
    totalD = Sum([If(in_city[D][i], 1, 0) for i in range(10)])
    totalF = Sum([If(in_city[F][i], 1, 0) for i in range(10)])
    totalK = Sum([If(in_city[K][i], 1, 0) for i in range(10)])
    solver.add(totalD == 7, totalF == 3, totalK == 2)
    
    # Days 9-10 entirely in Krakow
    solver.add(s[8] == K, s[9] == K, s[10] == K)  # Start of days 9,10,11
    solver.add(Not(flight[8]), Not(flight[9]))  # No flights on days 9-10
    
    # Exactly 2 flights
    solver.add(Sum([If(flight[i], 1, 0) for i in range(10)]) == 2)
    
    # Solve and format output
    if solver.check() == sat:
        m = solver.model()
        itinerary = []
        for day in range(10):
            present = []
            for c in [D, F, K]:
                if is_true(m.eval(in_city[c][day])):
                    present.append(cities[c])
            present.sort()
            itinerary.append({
                "day": day+1,
                "place": ", ".join(present)
            })
        
        # Group consecutive days
        grouped = []
        i = 0
        while i < 10:
            j = i
            while j < 10 and itinerary[j]["place"] == itinerary[i]["place"]:
                j += 1
            day_range = f"Day {i+1}-{j}" if j > i+1 else f"Day {i+1}"
            grouped.append({
                "day_range": day_range,
                "place": itinerary[i]["place"]
            })
            i = j
        
        print(json.dumps({"itinerary": grouped}))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()