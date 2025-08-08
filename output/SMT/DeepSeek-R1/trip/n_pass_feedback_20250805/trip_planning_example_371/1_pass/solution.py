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
    s = [Int('s%d' % i) for i in range(1, 10)]  # s0 = day1 start, s1 = day2 start, ..., s8 = day9 start
    
    solver = Solver()
    
    # Each day's start city must be one of the four cities
    for i in range(9):
        solver.add(s[i] >= 0, s[i] <= 3)
    
    # Define allowed flight pairs (bidirectional)
    allowed_edges = [(Nice, Stockholm), (Nice, Vienna), (Stockholm, Split), (Stockholm, Vienna), (Split, Vienna)]
    allowed_directed = []
    for a, b in allowed_edges:
        allowed_directed.append((a, b))
        allowed_directed.append((b, a))
    
    # Flight constraints for transitions between consecutive days (days 1-8)
    for i in range(8):
        current_city = s[i]
        next_city = s[i+1]
        # If the start city changes, ensure there's a direct flight
        flight_cond = Or([And(current_city == a, next_city == b) for (a, b) in allowed_directed])
        solver.add(If(current_city != next_city, flight_cond, True))
    
    # Specific day constraints:
    # Split must be visited on day 7 (set includes s6 and s7) and day 9 (s8)
    solver.add(Or(s[6] == Split, s[7] == Split))  # Day 7: cities s7 (s[6]) and s8 (s[7])
    solver.add(s[8] == Split)  # Day 9: city s9 (s[8])
    
    # Vienna must be visited on day 1 or day 2
    solver.add(Or(s[0] == Vienna, s[1] == Vienna, s[2] == Vienna))
    
    # Count total days per city
    def count_days(city):
        total = 0
        # Days 1-8: each day i contributes if the city is in {start_i, start_{i+1}}
        for i in range(8):
            total += If(Or(s[i] == city, s[i+1] == city), 1, 0)
        # Day 9: only the start city s8
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