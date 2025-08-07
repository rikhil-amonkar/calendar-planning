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
    
    # Create variables for the start city of each day (s0 to s8 for days 1 to 9)
    s = [Int('s%d' % i) for i in range(9)]  # s[0] for day1, s[1] for day2, ..., s[8] for day9
    
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
    
    # Flight constraints for transitions between consecutive days (days 1-8)
    for i in range(8):
        current_city = s[i]
        next_city = s[i+1]
        # If the start city changes, ensure there's a direct flight
        flight_cond = Or([And(current_city == a, next_city == b) for (a, b) in allowed_directed])
        solver.add(If(current_city != next_city, flight_cond, True))
    
    # Workshop in Vienna: must be in Vienna on both day1 and day2
    # Day1: either start in Vienna or fly to Vienna at the end of day1
    in_vienna_day1 = Or(s[0] == Vienna, And(s[0] != s[1], s[1] == Vienna))
    # Day2: either start in Vienna or fly to Vienna at the end of day2
    in_vienna_day2 = Or(s[1] == Vienna, And(s[1] != s[2], s[2] == Vienna))
    solver.add(in_vienna_day1, in_vienna_day2)
    
    # Conference in Split: must be in Split on day7 and day9
    # Day7: either start in Split or fly to Split at the end of day7
    in_split_day7 = Or(s[6] == Split, And(s[6] != s[7], s[7] == Split))
    # Day9: must start in Split (no flight after day9)
    in_split_day9 = (s[8] == Split)
    solver.add(in_split_day7, in_split_day9)
    
    # Count total days per city
    def count_days(city):
        total = 0
        # Days 1-8: each day i contributes if the city is the start of day i or the start of day i+1 (if flight occurs)
        for i in range(8):
            total += If(Or(s[i] == city, s[i+1] == city), 1, 0)
        # Day9: only the start city of day9
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
        
        # Build itinerary
        itinerary = []
        for day in range(1, 10):  # Days 1 to 9
            if day < 9:
                idx = day - 1
                c1 = s_val[idx]
                c2 = s_val[idx+1]
                if c1 == c2:
                    places = [city_names[c1]]
                else:
                    places = [city_names[c1], city_names[c2]]
            else:  # Day 9
                places = [city_names[s_val[8]]]
            itinerary.append({"day": day, "place": places})
        
        # Output as JSON
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()