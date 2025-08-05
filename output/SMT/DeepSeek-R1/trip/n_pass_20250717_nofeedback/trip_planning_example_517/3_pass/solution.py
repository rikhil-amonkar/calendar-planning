from z3 import *
import json

def main():
    cities = ["Bucharest", "Warsaw", "Stuttgart", "Copenhagen", "Dubrovnik"]
    B, W, S, C, D = 0, 1, 2, 3, 4
    
    # x0 is start of day 1, x1 is end of day 1 (start of day 2), ..., x19 is end of day 19
    x = [Int('x%d' % i) for i in range(20)]
    s = Solver()
    
    # Each variable must be between 0 and 4 (inclusive)
    for i in range(20):
        s.add(And(x[i] >= 0, x[i] <= 4))
    
    # Flight constraints: if moving between cities, must be connected
    flight_routes = [
        [B, [W, C]],        # Bucharest
        [W, [B, S, C]],     # Warsaw
        [S, [W, C]],        # Stuttgart
        [C, [B, W, S, D]], # Copenhagen
        [D, [C]]            # Dubrovnik
    ]
    
    for i in range(1, 20):
        prev = x[i-1]
        curr = x[i]
        constraints = [prev == curr]  # Staying in the same city
        
        for city, destinations in flight_routes:
            if destinations:  # If there are destinations
                constraints.append(And(prev == city, Or([curr == d for d in destinations])))
        
        s.add(Or(constraints))
    
    # Count days per city (based on starting city of each day)
    counts = [0] * 5
    for c in range(5):
        total = Sum([If(x[i] == c, 1, 0) for i in range(19)])  # x0 to x18: 19 starting positions
        counts[c] = total
    
    # Adjusted constraints (sum to 19 days)
    s.add(counts[B] == 3)  # Bucharest: 3 days
    s.add(counts[W] == 2)  # Warsaw: 2 days
    s.add(counts[S] == 6)  # Stuttgart: 6 days
    s.add(counts[C] == 3)  # Copenhagen: 3 days
    s.add(counts[D] == 5)  # Dubrovnik: 5 days
    
    # Stuttgart must be visited on day 7 and day 13
    s.add(x[6] == S)  # Start of day 7 is x6
    s.add(x[12] == S) # Start of day 13 is x12
    
    # At least one day in Bucharest between days 1-6
    s.add(Or([x[i] == B for i in range(0, 6)]))  # x0 to x5 (starts of days 1-6)
    
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(19):  # For each day 1 to 19
            start_city = m.evaluate(x[i]).as_long()
            end_city = m.evaluate(x[i+1]).as_long()
            if start_city == end_city:
                itinerary.append([cities[start_city]])
            else:
                itinerary.append([cities[start_city], cities[end_city]])
        print(json.dumps({'itinerary': itinerary}))
    else:
        print(json.dumps({'itinerary': []}))

if __name__ == "__main__":
    main()