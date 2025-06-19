from z3 import Solver, Int, And, sat

def main():
    # Initialize Z3 solver
    s = Solver()
    
    # Define variables for departure days
    leave_Naples = Int('leave_Naples')
    leave_Vienna = Int('leave_Vienna')
    
    # Add constraints
    s.add(leave_Naples >= 5, leave_Naples <= 17)
    s.add(leave_Vienna >= leave_Naples, leave_Vienna <= 17)
    s.add(leave_Naples == 5)  # Must leave Naples on day 5 to have exactly 5 days in Naples
    s.add(leave_Vienna - leave_Naples + 1 == 7)  # Vienna stay duration (7 days)
    s.add(17 - leave_Vienna + 1 == 7)  # Vilnius stay duration (7 days)
    
    # Check if constraints are satisfiable
    if s.check() == sat:
        m = s.model()
        leave_Naples_val = m[leave_Naples].as_long()
        leave_Vienna_val = m[leave_Vienna].as_long()
        
        # Construct itinerary
        itinerary = [
            {"day_range": "Day 1-5", "place": "Naples"},
            {"day_range": "Day 5", "place": "Naples"},
            {"day_range": "Day 5", "place": "Vienna"},
            {"day_range": "Day 5-11", "place": "Vienna"},
            {"day_range": "Day 11", "place": "Vienna"},
            {"day_range": "Day 11", "place": "Vilnius"},
            {"day_range": "Day 11-17", "place": "Vilnius"}
        ]
        
        # Output as JSON-formatted dictionary
        result = {"itinerary": itinerary}
        print(result)
    else:
        print("No valid itinerary found")

if __name__ == '__main__':
    main()