from z3 import *

def main():
    # Initialize solver
    s = Solver()
    
    # Define variables for transition days
    s2 = Int('s2')
    s3 = Int('s3')
    s4 = Int('s4')
    
    # Define city variables for each segment
    C1 = Int('C1')
    C2 = Int('C2')
    C3 = Int('C3')
    C4 = Int('C4')
    
    # Valid city sequences based on direct flights
    sequences = [
        [0, 2, 1, 3],  # London, Split, Oslo, Porto
        [2, 0, 1, 3],  # Split, London, Oslo, Porto
        [3, 1, 0, 2],  # Porto, Oslo, London, Split
        [3, 1, 2, 0]   # Porto, Oslo, Split, London
    ]
    
    # Add constraint that city sequence must be valid
    s.add(Or([
        And(C1 == seq[0], C2 == seq[1], C3 == seq[2], C4 == seq[3])
        for seq in sequences
    ]))
    
    # Constraints on transition days
    s.add(s2 >= 2, s2 <= 16)
    s.add(s3 >= 3, s3 <= 16)
    s.add(s4 >= 4, s4 <= 16)
    s.add(s2 < s3, s3 < s4)
    
    # Calculate days per city
    London_days = If(C1 == 0, s2, 0) + If(C2 == 0, s3 - s2 + 1, 0) + If(C3 == 0, s4 - s3 + 1, 0) + If(C4 == 0, 16 - s4 + 1, 0)
    Oslo_days = If(C1 == 1, s2, 0) + If(C2 == 1, s3 - s2 + 1, 0) + If(C3 == 1, s4 - s3 + 1, 0) + If(C4 == 1, 16 - s4 + 1, 0)
    Split_days = If(C1 == 2, s2, 0) + If(C2 == 2, s3 - s2 + 1, 0) + If(C3 == 2, s4 - s3 + 1, 0) + If(C4 == 2, 16 - s4 + 1, 0)
    Porto_days = If(C1 == 3, s2, 0) + If(C2 == 3, s3 - s2 + 1, 0) + If(C3 == 3, s4 - s3 + 1, 0) + If(C4 == 3, 16 - s4 + 1, 0)
    
    # Add constraints for total days per city
    s.add(London_days == 7)
    s.add(Oslo_days == 2)
    s.add(Split_days == 5)
    s.add(Porto_days == 5)
    
    # Constraint: Must be in Split from day 7 to 11
    for d in range(7, 12):
        in_split = Or(
            And(d < s2, C1 == 2),
            And(d == s2, Or(C1 == 2, C2 == 2)),
            And(d > s2, d < s3, C2 == 2),
            And(d == s3, Or(C2 == 2, C3 == 2)),
            And(d > s3, d < s4, C3 == 2),
            And(d == s4, Or(C3 == 2, C4 == 2)),
            And(d > s4, C4 == 2)
        )
        s.add(in_split)
    
    # Constraint: Must be in London between day 1 and 7
    london_constraints = []
    for d in range(1, 8):
        in_london = Or(
            And(d < s2, C1 == 0),
            And(d == s2, Or(C1 == 0, C2 == 0)),
            And(d > s2, d < s3, C2 == 0),
            And(d == s3, Or(C2 == 0, C3 == 0)),
            And(d > s3, d < s4, C3 == 0),
            And(d == s4, Or(C3 == 0, C4 == 0)),
            And(d > s4, C4 == 0)
        )
        london_constraints.append(in_london)
    s.add(Or(london_constraints))
    
    # Check satisfiability
    if s.check() == sat:
        m = s.model()
        # Get values from model
        s2_val = m[s2].as_long()
        s3_val = m[s3].as_long()
        s4_val = m[s4].as_long()
        cities = [m[C1].as_long(), m[C2].as_long(), m[C3].as_long(), m[C4].as_long()]
        city_names = {0: 'London', 1: 'Oslo', 2: 'Split', 3: 'Porto'}
        
        # Build itinerary segments
        itinerary = []
        segments = [
            (1, s2_val, cities[0]),
            (s2_val, s3_val, cities[1]),
            (s3_val, s4_val, cities[2]),
            (s4_val, 16, cities[3])
        ]
        
        for start, end, city_code in segments:
            place = city_names[city_code]
            if start == end:
                day_range = f"Day {start}"
            else:
                day_range = f"Day {start}-{end}"
            itinerary.append({"day_range": day_range, "place": place})
        
        # Output as JSON
        import json
        print(json.dumps({"itinerary": itinerary}))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()