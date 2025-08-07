from z3 import *
import json

def main():
    # City constants
    Nice = 0
    Stockholm = 1
    Split = 2
    Vienna = 3
    city_names = {
        Nice: "Nice",
        Stockholm: "Stockholm",
        Split: "Split",
        Vienna: "Vienna"
    }
    
    # Start city for each day (days 1-9)
    s = [Int(f's_{i}') for i in range(9)]
    solver = Solver()
    
    # City domain constraints
    for i in range(9):
        solver.add(s[i] >= Nice, s[i] <= Vienna)
    
    # Fixed constraints:
    solver.add(s[0] == Vienna)  # Day 1 start in Vienna
    solver.add(s[1] == Vienna)  # Day 2 start in Vienna
    solver.add(s[8] == Split)   # Day 9 start in Split
    
    # Must be in Split on day 7 (start or arrival)
    solver.add(Or(
        s[6] == Split,          # Start day 7 in Split
        And(s[7] == Split, s[6] != s[7])  # Arrive in Split on day 7
    ))
    
    # Flight connections (bidirectional)
    allowed_pairs = [
        (Vienna, Stockholm),
        (Vienna, Nice),
        (Vienna, Split),
        (Stockholm, Split),
        (Nice, Stockholm)
    ]
    directed_flights = []
    for a, b in allowed_pairs:
        directed_flights.append((a, b))
        directed_flights.append((b, a))
    
    # Flight constraints between consecutive days
    for i in range(8):
        current = s[i]
        next_city = s[i+1]
        solver.add(If(
            current != next_city,
            Or([And(current == a, next_city == b) for a, b in directed_flights]),
            True
        ))
    
    # Calculate days in each city (including travel days)
    days_in_city = {city: 0 for city in [Nice, Stockholm, Split, Vienna]}
    
    # Days 1-8: count start city and arrival city (if flying)
    for i in range(8):
        for city in [Nice, Stockholm, Split, Vienna]:
            # In city if: started there OR arrived there in evening
            solver.add(
                days_in_city[city] == 
                days_in_city[city] + 
                If(Or(s[i] == city, And(s[i+1] == city, s[i] != s[i+1])), 1, 0)
    
    # Day 9: only start city
    for city in [Nice, Stockholm, Split, Vienna]:
        solver.add(
            days_in_city[city] == 
            days_in_city[city] + If(s[8] == city, 1, 0)
    
    # Total days per city
    solver.add(days_in_city[Nice] == 2)
    solver.add(days_in_city[Stockholm] == 5)
    solver.add(days_in_city[Split] == 3)
    solver.add(days_in_city[Vienna] == 2)
    
    # Exactly 3 flight days (days with city change)
    num_flights = Sum([If(s[i] != s[i+1], 1, 0) for i in range(8)])
    solver.add(num_flights == 3)
    
    # Solve and output
    if solver.check() == sat:
        model = solver.model()
        s_vals = [model.evaluate(s_i).as_long() for s_i in s]
        
        # Group consecutive days with same start city
        itinerary = []
        start_idx = 0
        current_city = s_vals[0]
        
        for i in range(1, 9):
            if s_vals[i] != current_city:
                itinerary.append({
                    'day_range': f'Day {start_idx+1}-{i}',
                    'place': city_names[current_city]
                })
                start_idx = i
                current_city = s_vals[i]
        
        # Add last segment
        itinerary.append({
            'day_range': f'Day {start_idx+1}-9',
            'place': city_names[current_city]
        })
        
        print(json.dumps({'itinerary': itinerary}))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()