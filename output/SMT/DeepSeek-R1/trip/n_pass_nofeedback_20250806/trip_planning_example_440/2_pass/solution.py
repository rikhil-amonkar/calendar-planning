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
    
    # Fixed durations for each city
    duration = {
        Split: 2,
        Helsinki: 2,
        Reykjavik: 3,
        Vilnius: 3,
        Geneva: 6
    }
    
    # Direct flight connections (both directions)
    connections = [
        (Split, Helsinki),
        (Geneva, Split),
        (Geneva, Helsinki),
        (Helsinki, Reykjavik),
        (Vilnius, Helsinki),
        (Split, Vilnius)
    ]
    allowed_pairs = []
    for a, b in connections:
        allowed_pairs.append((a, b))
        allowed_pairs.append((b, a))
    
    # Position variables for the order of cities
    pos = [Const(f'pos_{i}', City) for i in range(5)]
    s = Solver()
    
    # Each city must appear exactly once
    s.add(Distinct(pos))
    
    # Start day variables
    start = [Int(f'start_{i}') for i in range(5)]
    s.add(start[0] == 1)
    for i in range(4):
        # Next city starts on the last day of the current city
        s.add(start[i+1] == start[i] + duration[pos[i]] - 1)
    s.add(start[4] + duration[pos[4]] - 1 == 12)  # Total days constraint
    
    # Consecutive cities must have a direct flight
    for i in range(4):
        constraints = []
        for a, b in allowed_pairs:
            constraints.append(And(pos[i] == a, pos[i+1] == b))
        s.add(Or(constraints))
    
    # Event constraints
    for i in range(5):
        s.add(If(pos[i] == Reykjavik, And(start[i] >= 8, start[i] <= 10), True))
        s.add(If(pos[i] == Vilnius, And(start[i] >= 5, start[i] <= 9), True))
    
    # Solve the constraints
    if s.check() == sat:
        m = s.model()
        itinerary_list = []
        # Build the itinerary
        for i in range(5):
            city_val = m.evaluate(pos[i])
            st_val = m.evaluate(start[i])
            st_val = st_val.as_long() if is_int_value(st_val) else st_val
            dur_val = duration[city_val]
            city_name = city_names[city_val]
            # Add each day in the city's duration to the itinerary
            for d in range(st_val, st_val + dur_val):
                itinerary_list.append({"day": d, "place": city_name})
        # Output as JSON
        result = {"itinerary": itinerary_list}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()