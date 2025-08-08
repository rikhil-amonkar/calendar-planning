from z3 import *

def main():
    # Define the durations for each segment
    d0 = Int('d0')  # Duration for Dublin (first segment)
    d1 = Int('d1')  # Duration for Riga (middle segment)
    d2 = Int('d2')  # Duration for Vilnius (last segment)
    
    s = Solver()
    # Constraints: first segment at least 2 days, middle at least 2, last at least 1
    s.add(d0 >= 2, d1 >= 2, d2 >= 1)
    # Total days must be 12
    s.add(d0 + d1 + d2 == 12)
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        d0_val = m[d0].as_long()
        d1_val = m[d1].as_long()
        d2_val = m[d2].as_long()
        
        # Compute start and end days for each segment
        start0 = 1
        end0 = start0 + d0_val - 1
        start1 = end0 + 1
        end1 = start1 + d1_val - 1
        start2 = end1 + 1
        end2 = start2 + d2_val - 1
        
        # Format day ranges
        def format_day_range(start, end):
            if start == end:
                return f"Day {start}"
            return f"Day {start}-{end}"
        
        itinerary = [
            {'day_range': format_day_range(start0, end0), 'place': 'Dublin'},
            {'day_range': format_day_range(start1, end1), 'place': 'Riga'},
            {'day_range': format_day_range(start2, end2), 'place': 'Vilnius'}
        ]
        
        plan = {'itinerary': itinerary}
        print(f"Plan found: {plan}")
    else:
        print("No valid plan found")

if __name__ == "__main__":
    main()