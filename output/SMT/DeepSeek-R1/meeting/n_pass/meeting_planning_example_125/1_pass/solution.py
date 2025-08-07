from z3 import *

def main():
    # Initialize solver
    s = Solver()
    
    # Define variables for start times (in minutes from 9:00 AM)
    s_start = Int('s_start')  # Start time for meeting with Stephanie
    j_start = Int('j_start')  # Start time for meeting with John
    
    # Calculate end times
    s_end = s_start + 90  # Stephanie meeting duration is exactly 90 minutes
    j_end = j_start + 30  # John meeting duration is exactly 30 minutes
    
    # Availability constraints
    # Stephanie must end by 11:30 AM (150 minutes from 9:00 AM)
    s.add(s_end <= 150)
    # Stephanie's start must be at least 5 minutes (arrive at Financial District at 9:05 AM)
    s.add(s_start >= 5)
    
    # John must start after 10:15 AM (75 minutes) and end by 8:45 PM (705 minutes)
    s.add(j_start >= 75)
    s.add(j_end <= 705)
    
    # Travel constraints for two possible orders
    # Order 1: Stephanie first, then John
    order1 = And(
        s_start >= 5,  # Travel to Financial District
        j_start >= s_end + 17  # Travel from Financial District to Alamo Square
    )
    
    # Order 2: John first, then Stephanie
    order2 = And(
        j_start >= 19,  # Travel to Alamo Square
        s_start >= j_end + 17  # Travel from Alamo Square to Financial District
    )
    
    # Either order must hold
    s.add(Or(order1, order2))
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        s_start_val = m.eval(s_start).as_long()
        s_end_val = s_start_val + 90
        j_start_val = m.eval(j_start).as_long()
        j_end_val = j_start_val + 30
        
        # Convert times to HH:MM format
        def format_time(minutes):
            total_minutes = minutes
            hours = total_minutes // 60
            minutes = total_minutes % 60
            return f"{hours:02d}:{minutes:02d}"
        
        # Create itinerary list
        itinerary = []
        # Stephanie meeting
        itinerary.append({
            "action": "meet",
            "person": "Stephanie",
            "start_time": format_time(s_start_val),
            "end_time": format_time(s_end_val)
        })
        # John meeting
        itinerary.append({
            "action": "meet",
            "person": "John",
            "start_time": format_time(j_start_val),
            "end_time": format_time(j_end_val)
        })
        
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: x["start_time"])
        
        # Output as JSON
        print({
            "itinerary": itinerary
        })
    else:
        print("No feasible schedule found")

if __name__ == "__main__":
    main()