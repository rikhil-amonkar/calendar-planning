from z3 import *
import json

def main():
    # Define city mappings
    Vienna, Stockholm, Nice, Split = 0, 1, 2, 3
    city_names = {
        Vienna: "Vienna",
        Stockholm: "Stockholm",
        Nice: "Nice",
        Split: "Split"
    }
    
    # Allowed direct flights (bidirectional)
    allowed_edges = [
        (Vienna, Stockholm), (Stockholm, Vienna),
        (Vienna, Nice), (Nice, Vienna),
        (Vienna, Split), (Split, Vienna),
        (Stockholm, Split), (Split, Stockholm),
        (Stockholm, Nice), (Nice, Stockholm)
    ]
    
    # Create Z3 variables
    s = [Int(f's_{i}') for i in range(9)]  # s[0] to s[8]: starting city for days 1 to 9
    f = [Bool(f'f_{i}') for i in range(8)]  # f[0] to f[7]: flight on days 1 to 8
    
    solver = Solver()
    
    # Constrain each s[i] to be one of the cities
    for i in range(9):
        solver.add(Or(s[i] == Vienna, s[i] == Stockholm, s[i] == Nice, s[i] == Split))
    
    # Flight constraints for days 1 to 8
    for i in range(8):
        edge_constraints = []
        for a, b in allowed_edges:
            edge_constraints.append(And(s[i] == a, s[i+1] == b))
        solver.add(If(f[i], Or(edge_constraints), s[i] == s[i+1]))
    
    # Split must be on day 9
    solver.add(s[8] == Split)
    
    # Split must be on day 7
    solver.add(Or(s[6] == Split, And(f[6], s[7] == Split)))
    
    # Vienna must be on at least one of day 1 or 2
    condition_day1 = Or(
        And(f[0], Or(s[0] == Vienna, s[1] == Vienna)),
        And(Not(f[0]), s[0] == Vienna)
    )
    condition_day2 = Or(
        And(f[1], Or(s[1] == Vienna, s[2] == Vienna)),
        And(Not(f[1]), s[1] == Vienna)
    )
    solver.add(Or(condition_day1, condition_day2))
    
    # Total days for each city
    vienna_count = 0
    stockholm_count = 0
    nice_count = 0
    split_count = 0
    
    for i in range(8):
        # For flight days
        vienna_count += If(f[i], 
                          (If(s[i] == Vienna, 1, 0) + If(s[i+1] == Vienna, 1, 0)),
                          If(s[i] == Vienna, 1, 0))
        stockholm_count += If(f[i], 
                             (If(s[i] == Stockholm, 1, 0) + If(s[i+1] == Stockholm, 1, 0)),
                             If(s[i] == Stockholm, 1, 0))
        nice_count += If(f[i], 
                        (If(s[i] == Nice, 1, 0) + If(s[i+1] == Nice, 1, 0)),
                        If(s[i] == Nice, 1, 0))
        split_count += If(f[i], 
                         (If(s[i] == Split, 1, 0) + If(s[i+1] == Split, 1, 0)),
                         If(s[i] == Split, 1, 0))
    
    # Add day 9 (no flight)
    vienna_count += If(s[8] == Vienna, 1, 0)
    stockholm_count += If(s[8] == Stockholm, 1, 0)
    nice_count += If(s[8] == Nice, 1, 0)
    split_count += If(s[8] == Split, 1, 0)
    
    solver.add(vienna_count == 2)
    solver.add(stockholm_count == 5)
    solver.add(nice_count == 2)
    solver.add(split_count == 3)
    
    # Check and get the model
    if solver.check() == sat:
        model = solver.model()
        
        # Extract the values for s and f
        s_vals = [model.evaluate(s[i]).as_long() for i in range(9)]
        f_vals = [model.evaluate(f[i]) for i in range(8)]
        
        # Build itinerary
        itinerary = []
        for day in range(1, 10):  # day from 1 to 9
            if day < 9 and is_true(f_vals[day-1]):
                start_city = s_vals[day-1]
                end_city = s_vals[day]
                cities = [city_names[start_city], city_names[end_city]]
            else:
                city = s_vals[day-1]
                cities = [city_names[city]]
            itinerary.append({"day": day, "city": cities})
        
        # Output as JSON
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()