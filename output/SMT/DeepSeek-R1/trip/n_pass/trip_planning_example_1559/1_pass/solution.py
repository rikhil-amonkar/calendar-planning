from z3 import *

def main():
    # Cities in the chain after Seville (excluding the fixed first and last)
    cities_after = ['Oslo', 'Lyon', 'Paris', 'Nice', 'Tallinn']
    # Durations: index 0: Oslo->3, 1: Lyon->4, 2: Paris->4, 3: Nice->4, 4: Tallinn->2
    durations = [3, 4, 4, 4, 2]
    
    # Fixed first and last in the chain: Paris (index2) and Nice (index3)
    idx0_fixed = 2  # Paris
    idx4_fixed = 3  # Nice
    
    # Variables for the three middle positions
    idx1 = Int('idx1')
    idx2 = Int('idx2')
    idx3 = Int('idx3')
    
    s = Solver()
    
    # Ensure indices are distinct and within {0,1,4}
    s.add(Distinct(idx1, idx2, idx3))
    s.add(Or(idx1 == 0, idx1 == 1, idx1 == 4))
    s.add(Or(idx2 == 0, idx2 == 1, idx2 == 4))
    s.add(Or(idx3 == 0, idx3 == 1, idx3 == 4))
    
    # Flight constraints: between consecutive cities
    # From idx1 to idx2: valid if (0,1), (0,4), (1,0), (4,0)
    s.add(Or(
        And(idx1 == 0, Or(idx2 == 1, idx2 == 4)),
        And(idx1 == 1, idx2 == 0),
        And(idx1 == 4, idx2 == 0)
    ))
    
    # From idx2 to idx3
    s.add(Or(
        And(idx2 == 0, Or(idx3 == 1, idx3 == 4)),
        And(idx2 == 1, idx3 == 0),
        And(idx2 == 4, idx3 == 0)
    ))
    
    # From idx3 to Nice: Nice is index3 in cities_after, but we need the flight to 'Nice'
    # Only Oslo (0) and Lyon (1) connect to Nice
    s.add(Or(idx3 == 0, idx3 == 1))
    
    # Duration for the three cities
    dur1 = If(idx1 == 0, 3, If(idx1 == 1, 4, 2))
    dur2 = If(idx2 == 0, 3, If(idx2 == 1, 4, 2))
    dur3 = If(idx3 == 0, 3, If(idx3 == 1, 4, 2))
    
    # If Oslo is at position3 (idx3==0), then its start day must be in [11,15]
    start3 = 10 + dur1 + dur2  # s3 = 10 + dur1 + dur2
    s.add(If(idx3 == 0, And(start3 >= 11, start3 <= 15), True)
    
    # Solve the constraints
    if s.check() == sat:
        m = s.model()
        idx1_val = m[idx1].as_long()
        idx2_val = m[idx2].as_long()
        idx3_val = m[idx3].as_long()
        
        # Build the chain of cities
        chain_cities = [
            cities_after[idx0_fixed],  # Paris
            cities_after[idx1_val],    # first middle city
            cities_after[idx2_val],    # second middle city
            cities_after[idx3_val],    # third middle city
            cities_after[idx4_fixed]   # Nice
        ]
        
        # Durations for the chain
        chain_durations = [
            4,  # Paris
            durations[idx1_val],
            durations[idx2_val],
            durations[idx3_val],
            4   # Nice
        ]
        
        # Compute start and end days for the chain
        starts = [9]  # first city in chain starts at day9
        ends = [9 + chain_durations[0] - 1]
        
        for i in range(1, 5):
            starts.append(ends[i-1])  # next city starts the day the previous ended
            ends.append(starts[i] + chain_durations[i] - 1)
        
        # Fixed part of the trip: before the chain
        fixed_schedule = [
            ('Prague', 1, 3),
            ('Valencia', 3, 4),
            ('Lisbon', 4, 5),
            ('Seville', 5, 9)
        ]
        
        # Chain part
        chain_schedule = []
        for i in range(5):
            chain_schedule.append((chain_cities[i], starts[i], ends[i]))
        
        # Mykonos after the chain
        mykonos_start = ends[-1]  # last day of Nice is the start for Mykonos
        mykonos_end = mykonos_start + 5 - 1
        final_schedule = fixed_schedule + chain_schedule + [('Mykonos', mykonos_start, mykonos_end)]
        
        # Output the schedule
        print("Trip Schedule:")
        for entry in final_schedule:
            print(f"{entry[0]}: days {entry[1]} to {entry[2]}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()