from z3 import *
import json

def main():
    cities = ["Bucharest", "Warsaw", "Stuttgart", "Copenhagen", "Dubrovnik"]
    B, W, S, C, D = 0, 1, 2, 3, 4
    
    # Define flight routes as a list of lists
    flight_routes = [
        [W, C],         # Bucharest (0)
        [B, S, C],      # Warsaw (1)
        [W, C],         # Stuttgart (2)
        [B, W, S, D],   # Copenhagen (3)
        [C]             # Dubrovnik (4)
    ]
    
    # Create 20 variables for the 19-day trip (start and end of each day)
    x = [Int('x%d' % i) for i in range(20)]
    s = Solver()
    
    # Each variable must be between 0 and 4 (inclusive)
    for i in range(20):
        s.add(And(x[i] >= 0, x[i] <= 4))
    
    # Flight constraints between consecutive days
    for i in range(19):  # 19 transitions between the 20 variables
        prev = x[i]
        curr = x[i+1]
        # Create disjunction for all possible flight routes
        route_disj = []
        for c in range(5):
            for d in flight_routes[c]:
                route_disj.append(And(prev == c, curr == d))
        # Either stay in the same city or take a valid flight
        s.add(Or(prev == curr, Or(route_disj)))
    
    # Count days per city (each day is represented by its starting city)
    counts = [0] * 5
    for c in range(5):
        # Sum over first 19 variables (days 1-19)
        total = Sum([If(x[i] == c, 1, 0) for i in range(19)])
        counts[c] = total
    
    # Add constraints for days in each city
    s.add(counts[B] == 3)  # Bucharest
    s.add(counts[W] == 2)  # Warsaw
    s.add(counts[S] == 6)  # Stuttgart
    s.add(counts[C] == 3)  # Copenhagen
    s.add(counts[D] == 5)  # Dubrovnik
    
    # Specific day constraints
    s.add(x[6] == S)   # Day 7 must be in Stuttgart
    s.add(x[12] == S)  # Day 13 must be in Stuttgart
    s.add(Or([x[i] == B for i in range(6)]))  # Bucharest in first 6 days
    
    if s.check() == sat:
        m = s.model()
        # Extract the starting city for each day
        day_cities = [m.evaluate(x[i]).as_long() for i in range(19)]
        
        # Group consecutive days with the same city
        segments = []
        start_idx = 0
        for i in range(1, 19):
            if day_cities[i] != day_cities[i-1]:
                # Add segment from start_idx to i-1
                start_day = start_idx + 1
                end_day = i
                segments.append((start_day, end_day, day_cities[start_idx]))
                start_idx = i
        # Add the last segment
        segments.append((start_idx + 1, 19, day_cities[start_idx]))
        
        # Format the itinerary
        itinerary = []
        for start, end, city_idx in segments:
            if start == end:
                day_range = f"Day {start}"
            else:
                day_range = f"Day {start}-{end}"
            itinerary.append({
                'day_range': day_range,
                'place': cities[city_idx]
            })
        
        print(json.dumps({'itinerary': itinerary}))
    else:
        print(json.dumps({'itinerary': []}))

if __name__ == "__main__":
    main()