from z3 import *

def main():
    # Initialize Z3 solver
    s = Solver()
    
    # Time in minutes from 9:00 AM
    m_start = Int('m_start')  # Start time for meeting Melissa
    a_start = Int('a_start')  # Start time for meeting Anthony
    
    # Constraints for Melissa
    s.add(m_start >= 29)  # Earliest arrival at North Beach
    s.add(m_start + 105 <= 270)  # Must end by 1:30 PM (270 minutes from 9:00 AM)
    
    # Constraints for Anthony
    s.add(a_start >= m_start + 105 + 6)  # Travel from North Beach to Chinatown takes 6 minutes
    s.add(a_start >= 255)  # Anthony available from 1:15 PM (255 minutes)
    s.add(a_start <= 270)  # Must start by 2:00 PM to end by 2:30 PM (270 minutes)
    
    # Check for a feasible solution
    if s.check() == sat:
        model = s.model()
        m_val = model.eval(m_start).as_long()
        a_val = model.eval(a_start).as_long()
        
        # Convert times from minutes to HH:MM format (from 9:00 AM base)
        def minutes_to_time(minutes):
            total_minutes = 540 + minutes  # 9:00 AM is 540 minutes from midnight
            hours = total_minutes // 60
            minutes = total_minutes % 60
            return f"{hours:02d}:{minutes:02d}"
        
        # Melissa meeting
        melissa_start = minutes_to_time(m_val)
        melissa_end = minutes_to_time(m_val + 105)
        
        # Anthony meeting
        anthony_start = minutes_to_time(a_val)
        anthony_end = minutes_to_time(a_val + 60)
        
        # Rebecca meeting (fixed from 7:30 PM to 9:15 PM)
        rebecca_start = "19:30"
        rebecca_end = "21:15"
        
        # Construct itinerary in chronological order
        itinerary = [
            {"action": "meet", "person": "Melissa", "start_time": melissa_start, "end_time": melissa_end},
            {"action": "meet", "person": "Anthony", "start_time": anthony_start, "end_time": anthony_end},
            {"action": "meet", "person": "Rebecca", "start_time": rebecca_start, "end_time": rebecca_end}
        ]
        
        # Output the solution
        print("SOLUTION:")
        print(f'{{"itinerary": {itinerary}}}')
    else:
        print("No solution found")

if __name__ == "__main__":
    main()