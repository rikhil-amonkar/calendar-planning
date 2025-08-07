from z3 import *
import json

def main():
    # Define city constants
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
    
    # Create variables for the start city of each day (days 1 to 9)
    s = [Int('s%d' % i) for i in range(9)]
    
    solver = Solver()
    
    # Each day's start city must be one of the four cities
    for i in range(9):
        solver.add(s[i] >= Nice, s[i] <= Vienna)
    
    # Fixed constraints: Vienna on days 1 and 2, Split on days 7 and 9
    solver.add(s[0] == Vienna)  # Day 1
    solver.add(s[1] == Vienna)  # Day 2
    solver.add(s[6] == Split)   # Day 7
    solver.add(s[8] == Split)   # Day 9
    
    # Define allowed flight pairs (bidirectional)
    allowed_pairs = [
        (Vienna, Stockholm),
        (Vienna, Nice),
        (Vienna, Split),
        (Stockholm, Split),
        (Nice, Stockholm)
    ]
    allowed_directed = []
    for a, b in allowed_pairs:
        allowed_directed.append((a, b))
        allowed_directed.append((b, a))
    
    # Flight constraints between consecutive days
    for i in range(8):
        current_city = s[i]
        next_city = s[i+1]
        flight_cond = Or([And(current_city == a, next_city == b) for (a, b) in allowed_directed])
        solver.add(If(current_city != next_city, flight_cond, True))
    
    # Total days per city (count start city for each day)
    total_nice = Sum([If(s[i] == Nice, 1, 0) for i in range(9)])
    total_stockholm = Sum([If(s[i] == Stockholm, 1, 0) for i in range(9)])
    total_split = Sum([If(s[i] == Split, 1, 0) for i in range(9)])
    total_vienna = Sum([If(s[i] == Vienna, 1, 0) for i in range(9)])
    
    solver.add(total_nice == 2)
    solver.add(total_stockholm == 5)
    solver.add(total_split == 3)
    solver.add(total_vienna == 2)
    
    # Solve the constraints
    if solver.check() == sat:
        model = solver.model()
        s_val = [model.evaluate(s[i]).as_long() for i in range(9)]
        
        # Group consecutive days with the same city into stays
        stays = []
        i = 0
        while i < 9:
            j = i
            # Traverse while the next day has the same starting city
            while j < 8 and s_val[j] == s_val[j+1]:
                j += 1
            start_day = i + 1
            end_day = j + 1
            stays.append({
                'day_range': f'Day {start_day}-{end_day}',
                'place': city_names[s_val[i]]
            })
            i = j + 1
        
        # Output as JSON
        result = {'itinerary': stays}
        print(json.dumps(result))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()