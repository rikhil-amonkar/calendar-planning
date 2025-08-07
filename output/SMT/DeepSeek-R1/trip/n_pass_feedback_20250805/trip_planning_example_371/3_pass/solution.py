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
    
    # Workshop in Vienna: must be in Vienna on day 1 and day 2
    in_vienna_day1 = Or(s[0] == Vienna, And(s[0] != s[1], s[1] == Vienna))
    in_vienna_day2 = Or(s[1] == Vienna, And(s[1] != s[2], s[2] == Vienna))
    solver.add(in_vienna_day1, in_vienna_day2)
    
    # Conference in Split: must be in Split on day 7 and day 9
    in_split_day7 = Or(s[6] == Split, And(s[6] != s[7], s[7] == Split))
    in_split_day9 = (s[8] == Split)
    solver.add(in_split_day7, in_split_day9)
    
    # Count total days per city
    def count_days(city):
        total = 0
        for i in range(8):
            total += If(Or(s[i] == city, s[i+1] == city), 1, 0)
        total += If(s[8] == city, 1, 0)
        return total
    
    solver.add(count_days(Nice) == 2)
    solver.add(count_days(Stockholm) == 5)
    solver.add(count_days(Split) == 3)
    solver.add(count_days(Vienna) == 2)
    
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