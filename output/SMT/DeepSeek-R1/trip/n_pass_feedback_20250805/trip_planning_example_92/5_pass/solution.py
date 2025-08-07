from z3 import *

def main():
    # Define segment durations as integers
    d_dublin = Int('d_dublin')
    d_riga = Int('d_riga')
    d_vilnius = Int('d_vilnius')
    
    s = Solver()
    # Apply constraints
    s.add(d_dublin >= 2)         # Dublin must have at least 2 days
    s.add(d_riga >= 2)           # Riga must have at least 2 days
    s.add(d_vilnius >= 1)        # Vilnius must have at least 1 day
    s.add(d_dublin + d_riga + d_vilnius == 12)  # Total trip duration
    
    if s.check() == sat:
        m = s.model()
        # Get actual duration values
        dublin_days = m[d_dublin].as_long()
        riga_days = m[d_riga].as_long()
        vilnius_days = m[d_vilnius].as_long()
        
        # Calculate start/end days for each segment
        dublin_start = 1
        dublin_end = dublin_days
        riga_start = dublin_end + 1
        riga_end = riga_start + riga_days - 1
        vilnius_start = riga_end + 1
        vilnius_end = 12
        
        # Helper function to format day ranges
        def format_days(start, end):
            return f"Day {start}" if start == end else f"Day {start}-{end}"
        
        # Build itinerary
        itinerary = [
            {'day_range': format_days(dublin_start, dublin_end), 'place': 'Dublin'},
            {'day_range': format_days(riga_start, riga_end), 'place': 'Riga'},
            {'day_range': format_days(vilnius_start, vilnius_end), 'place': 'Vilnius'}
        ]
        
        plan = {'itinerary': itinerary}
        print(f"Plan found: {plan}")
    else:
        print("No valid plan found")

if __name__ == "__main__":
    main()