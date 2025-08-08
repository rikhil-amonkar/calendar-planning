from z3 import *
import json

def main():
    cities = ["Bucharest", "Warsaw", "Stuttgart", "Copenhagen", "Dubrovnik"]
    B, W, S, C, D = 0, 1, 2, 3, 4
    
    # Variables: x0 to x19 represent start/end of days
    x = [Int('x%d' % i) for i in range(20)]
    s = Solver()
    
    # Each variable must be a valid city
    for i in range(20):
        s.add(And(x[i] >= 0, x[i] <= 4))
    
    # Flight constraints between connected cities
    flight_routes = {
        B: [W, C],        # Bucharest
        W: [B, S, C],     # Warsaw
        S: [W, C],        # Stuttgart
        C: [B, W, S, D],  # Copenhagen
        D: [C]            # Dubrovnik
    }
    
    for i in range(1, 20):
        prev = x[i-1]
        curr = x[i]
        # Can stay in same city or fly to connected city
        s.add(Or(
            prev == curr,
            And(prev != curr, Or([curr == dest for dest in flight_routes[prev.as_long()]]))
        ))
    
    # Correct day counting: count day if city appears at start OR end
    counts = [0] * 5
    for c in range(5):
        total = 0
        for i in range(1, 20):  # For each day 1-19
            total += If(Or(x[i-1] == c, x[i] == c), 1, 0)
        counts[c] = total
    
    # Adjusted constraints to sum to 19 days
    s.add(counts[B] == 3)  # Bucharest: 3 days
    s.add(counts[W] == 2)  # Warsaw: 2 days
    s.add(counts[S] == 6)  # Stuttgart: 6 days
    s.add(counts[C] == 3)  # Copenhagen: 3 days
    s.add(counts[D] == 5)  # Dubrovnik: 5 days
    
    # Stuttgart must be visited on day 7 and 13
    s.add(x[6] == S)  # Start of day 7
    s.add(x[12] == S)  # Start of day 13
    
    # At least one day in Bucharest between days 1-6
    s.add(Or([Or(x[i] == B, x[i+1] == B) for i in range(0, 6)]))
    
    if s.check() == sat:
        m = s.model()
        # Get end cities for days 1-19 (x1 to x19)
        end_cities = [m.evaluate(x[i]).as_long() for i in range(1, 20)]
        
        # Group consecutive days with same end city
        segments = []
        current_city = end_cities[0]
        start_day = 1
        for day in range(1, 19):
            if end_cities[day] != current_city:
                end_day = day
                segments.append((start_day, end_day, current_city))
                current_city = end_cities[day]
                start_day = day + 1
        segments.append((start_day, 19, current_city))
        
        # Format the itinerary
        itinerary_dicts = []
        for start, end, city_idx in segments:
            day_range = f"Day {start}-{end}" if start != end else f"Day {start}"
            itinerary_dicts.append({
                'day_range': day_range,
                'place': cities[city_idx]
            })
        
        print(json.dumps({'itinerary': itinerary_dicts}))
    else:
        print(json.dumps({'itinerary': []}))

if __name__ == "__main__":
    main()