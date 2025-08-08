from z3 import *

def main():
    # Initialize solver
    s = Solver()
    
    # Define variables
    s_start = Int('s_start')
    j_start = Int('j_start')
    order1 = Bool('order1')  # True: Stephanie first, False: John first
    
    # Meeting durations
    s_duration = 90
    j_duration = 30
    s_end = s_start + s_duration
    j_end = j_start + j_duration
    
    # Availability constraints
    s_available_end = 150  # 11:30 AM in minutes from 9:00 AM
    j_available_start = 75  # 10:15 AM
    j_available_end = 705   # 8:45 PM
    
    constraints = [
        s_start >= 0,  # Cannot start before 9:00 AM
        s_end <= s_available_end,
        j_start >= j_available_start,
        j_end <= j_available_end,
    ]
    
    # Travel constraints based on order
    travel_emb_to_fin = 5
    travel_emb_to_alamo = 19
    travel_fin_to_alamo = 17
    travel_alamo_to_fin = 17
    
    order_constraint = If(
        order1,
        And(
            s_start >= travel_emb_to_fin,
            j_start >= s_end + travel_fin_to_alamo
        ),
        And(
            j_start >= travel_emb_to_alamo,
            s_start >= j_end + travel_alamo_to_fin
        )
    )
    constraints.append(order_constraint)
    
    # Add all constraints to solver
    for c in constraints:
        s.add(c)
    
    # Check for solution
    if s.check() == sat:
        model = s.model()
        s_start_val = model.eval(s_start).as_long()
        j_start_val = model.eval(j_start).as_long()
        
        # Calculate end times
        s_end_val = s_start_val + s_duration
        j_end_val = j_start_val + j_duration
        
        # Convert times to HH:MM format
        def format_time(minutes):
            total_minutes = minutes
            hour = 9 + total_minutes // 60
            minute = total_minutes % 60
            return f"{hour:02d}:{minute:02d}"
        
        s_start_str = format_time(s_start_val)
        s_end_str = format_time(s_end_val)
        j_start_str = format_time(j_start_val)
        j_end_str = format_time(j_end_val)
        
        # Create meeting entries
        stephanie_meeting = {
            "action": "meet",
            "person": "Stephanie",
            "start_time": s_start_str,
            "end_time": s_end_str
        }
        john_meeting = {
            "action": "meet",
            "person": "John",
            "start_time": j_start_str,
            "end_time": j_end_str
        }
        
        # Sort meetings by start time
        meetings = [stephanie_meeting, john_meeting]
        meetings_sorted = sorted(meetings, key=lambda x: x['start_time'])
        
        # Output in required JSON format
        result = {"itinerary": meetings_sorted}
        print("SOLUTION:")
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()