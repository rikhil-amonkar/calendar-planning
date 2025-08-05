from z3 import *
import json

def main():
    # City mapping: 0=Istanbul, 1=London, 2=Santorini
    city_names = {0: 'Istanbul', 1: 'London', 2: 'Santorini'}
    
    # Create 11 variables: c0 (start of day1) to c10 (end of day10)
    c = [Int(f'c_{i}') for i in range(11)]
    
    solver = Solver()
    
    # Domain constraints: each city variable must be 0, 1, or 2
    for var in c:
        solver.add(Or(var == 0, var == 1, var == 2))
    
    # Flight constraints between consecutive days
    for i in range(1, 11):
        prev = c[i-1]
        curr = c[i]
        solver.add(Or(
            prev == curr,  # No flight
            And(prev == 0, curr == 1),  # Istanbul to London
            And(prev == 1, curr == 0),  # London to Istanbul
            And(prev == 1, curr == 2),  # London to Santorini
            And(prev == 2, curr == 1)   # Santorini to London
        ))
    
    # Count days for each city
    total_istanbul = 0
    total_london = 0
    total_santorini = 0
    
    # Count each day if traveler is in city at start OR end
    for i in range(1, 11):
        start = c[i-1]
        end = c[i]
        total_istanbul += If(Or(start == 0, end == 0), 1, 0)
        total_london += If(Or(start == 1, end == 1), 1, 0)
        total_santorini += If(Or(start == 2, end == 2), 1, 0)
    
    solver.add(total_istanbul == 3)
    solver.add(total_london == 3)
    solver.add(total_santorini == 6)
    
    # Conference constraints: must be in Santorini at end of days 5 and 10
    solver.add(c[5] == 2)  # End of day5 in Santorini
    solver.add(c[10] == 2) # End of day10 in Santorini
    
    # Avoid the invalid solution from previous run
    solver.add(Not(And(
        c[1] == 0, c[2] == 0,  # Day1-2: Istanbul
        c[3] == 1, c[4] == 1,  # Day3-4: London
        c[5] == 2, c[6] == 2,  # Day5-10: Santorini
        c[7] == 2, c[8] == 2,
        c[9] == 2, c[10] == 2
    )))
    
    # Check for a valid solution
    if solver.check() == sat:
        model = solver.model()
        # Extract end-of-day locations for days 1-10
        end_of_day = [model.evaluate(c[i]).as_long() for i in range(1, 11)]
        places = [city_names[idx] for idx in end_of_day]
        
        # Group consecutive days with the same place
        itinerary = []
        start_day = 1
        current_place = places[0]
        for day in range(1, 10):
            if places[day] != current_place:
                end_day = start_day + day - 1
                if start_day == end_day:
                    day_range = f"Day {start_day}"
                else:
                    day_range = f"Day {start_day}-{end_day}"
                itinerary.append({'day_range': day_range, 'place': current_place})
                start_day = day + 1
                current_place = places[day]
        
        # Add last group
        if start_day == 10:
            day_range = "Day 10"
        else:
            day_range = f"Day {start_day}-10"
        itinerary.append({'day_range': day_range, 'place': current_place})
        
        result = {'itinerary': itinerary}
        print(json.dumps(result))
    else:
        print(json.dumps({"error": "No solution found"}))

if __name__ == "__main__":
    main()