from z3 import *
import json

def main():
    # Define the city enumeration
    City, (Split, Helsinki, Reykjavik, Vilnius, Geneva) = EnumSort('City', ['Split', 'Helsinki', 'Reykjavik', 'Vilnius', 'Geneva'])
    
    # Mapping from enum to string names
    city_names = {
        Split: 'Split',
        Helsinki: 'Helsinki',
        Reykjavik: 'Reykjavik',
        Vilnius: 'Vilnius',
        Geneva: 'Geneva'
    }
    
    # Define the position variables (order of cities)
    pos = [Const(f'pos_{i}', City) for i in range(5)]
    
    # Define duration variables
    d = [Int(f'd_{i}') for i in range(5)]
    
    # Initialize solver
    s = Solver()
    
    # Set durations based on city
    for i in range(5):
        s.add(d[i] == If(pos[i] == Split, 2,
                         If(pos[i] == Helsinki, 2,
                         If(pos[i] == Reykjavik, 3,
                         If(pos[i] == Vilnius, 3, 6)))))
    
    # Each city visited exactly once
    s.add(Distinct(pos))
    
    # Define allowed direct flights (both directions)
    allowed_pairs = []
    flights = [
        ('Split', 'Helsinki'),
        ('Geneva', 'Split'),
        ('Geneva', 'Helsinki'),
        ('Helsinki', 'Reykjavik'),
        ('Vilnius', 'Helsinki'),
        ('Split', 'Vilnius')
    ]
    str_to_enum = {name: enum for name, enum in zip(['Split', 'Helsinki', 'Reykjavik', 'Vilnius', 'Geneva'], [Split, Helsinki, Reykjavik, Vilnius, Geneva])}
    for a, b in flights:
        a_enum = str_to_enum[a]
        b_enum = str_to_enum[b]
        allowed_pairs.append((a_enum, b_enum))
        allowed_pairs.append((b_enum, a_enum))
    
    # Consecutive cities must have a direct flight
    for i in range(4):
        constraints = []
        for a, b in allowed_pairs:
            constraints.append(And(pos[i] == a, pos[i+1] == b))
        s.add(Or(constraints))
    
    # Define start days for each city
    start = [Int(f'start_{i}') for i in range(5)]
    s.add(start[0] == 1)
    for i in range(1, 5):
        s.add(start[i] == start[i-1] + d[i-1] - 1)
    
    # Constraints for Reykjavik and Vilnius events
    for i in range(5):
        # Reykjavik must have a day between 10 and 12
        s.add(If(pos[i] == Reykjavik,
                 And(start[i] <= 12, start[i] + d[i] - 1 >= 10),
                 True))
        # Vilnius must have a day between 7 and 9
        s.add(If(pos[i] == Vilnius,
                 And(start[i] <= 9, start[i] + d[i] - 1 >= 7),
                 True))
    
    # Total days must be 12
    s.add(start[4] + d[4] - 1 == 12)
    
    # Solve the constraints
    if s.check() == sat:
        m = s.model()
        # Extract positions and durations
        pos_val = [m.evaluate(pos[i]) for i in range(5)]
        d_val = [m.evaluate(d[i]) for i in range(5)]
        # Convert to Python types
        d_val = [d_val_i.as_long() for d_val_i in d_val]
        # Compute start days
        start_val = [1]
        for i in range(4):
            start_val.append(start_val[-1] + d_val[i] - 1)
        # Build itinerary
        itinerary = []
        for day in range(1, 13):
            for i in range(5):
                s_i = start_val[i]
                e_i = s_i + d_val[i] - 1
                if s_i <= day <= e_i:
                    city = city_names[pos_val[i]]
                    itinerary.append({"day": day, "place": city})
        # Output as JSON
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()