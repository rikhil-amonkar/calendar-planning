from z3 import *

def main():
    s = Solver()
    
    # Define start time variables (in minutes from 9:00 AM)
    D_start = Int('D_start')  # Daniel at Golden Gate Park
    M_start = Int('M_start')  # Margaret at Russian Hill
    C_start = Int('C_start')  # Charles at Alamo Square
    
    # End times (fixed durations: Daniel 15min, Margaret 30min, Charles 90min)
    D_end = D_start + 15
    M_end = M_start + 30
    C_end = C_start + 90
    S_start = 690  # Stephanie fixed start: 8:30 PM (690 minutes from 9:00 AM)
    S_end = 780   # Stephanie end: 10:00 PM
    
    # Charles must start between 6:00 PM (540) and 7:50 PM (590)
    s.add(C_start >= 540, C_start <= 590)
    
    # Daniel must end by 1:30 PM (270 minutes)
    s.add(D_end <= 270)
    
    # Margaret must end by 4:00 PM (420 minutes)
    s.add(M_end <= 420)
    
    # Order flag: True if Daniel first, False if Margaret first
    order = Bool('order')
    
    # Constraints for Daniel first
    s.add(Implies(order, D_start >= 11))  # Travel Sunset to Golden Gate Park: 11 min
    s.add(Implies(order, M_start >= D_end + 19))  # Travel Golden Gate Park to Russian Hill: 19 min
    s.add(Implies(order, C_start >= M_end + 15))  # Travel Russian Hill to Alamo Square: 15 min
    
    # Constraints for Margaret first
    s.add(Implies(Not(order), M_start >= 24))  # Travel Sunset to Russian Hill: 24 min
    s.add(Implies(Not(order), D_start >= M_end + 21))  # Travel Russian Hill to Golden Gate Park: 21 min
    s.add(Implies(Not(order), C_start >= D_end + 10))  # Travel Golden Gate Park to Alamo Square: 10 min
    
    # Ensure non-negative start times
    s.add(D_start >= 0, M_start >= 0, C_start >= 0)
    
    # Check for a solution
    if s.check() == sat:
        model = s.model()
        d_start_val = model.eval(D_start).as_long()
        m_start_val = model.eval(M_start).as_long()
        c_start_val = model.eval(C_start).as_long()
        
        # Convert times to HH:MM format
        def format_time(minutes):
            total_minutes = minutes
            hours = total_minutes // 60
            minutes = total_minutes % 60
            # Since base is 9:00 AM, add hours to 9
            abs_hour = 9 + hours
            abs_minutes = minutes
            return f"{abs_hour:02d}:{abs_minutes:02d}"
        
        # Meetings in chronological order
        meetings = [
            {"action": "meet", "person": "Daniel", "start_time": format_time(d_start_val), "end_time": format_time(d_start_val + 15)},
            {"action": "meet", "person": "Margaret", "start_time": format_time(m_start_val), "end_time": format_time(m_start_val + 30)},
            {"action": "meet", "person": "Charles", "start_time": format_time(c_start_val), "end_time": format_time(c_start_val + 90)},
            {"action": "meet", "person": "Stephanie", "start_time": "20:30", "end_time": "22:00"}
        ]
        
        # Sort meetings by start time
        meetings_sorted = sorted(meetings, key=lambda x: x['start_time'])
        
        # Output as JSON
        result = {"itinerary": meetings_sorted}
        print(f"SOLUTION: {result}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()