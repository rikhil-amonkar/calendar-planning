from z3 import *

def main():
    T1 = Int('T1')  # Time leaving Golden Gate Park (in minutes from midnight)
    T2 = Int('T2')  # Time leaving Chinatown (in minutes from midnight)
    
    s = Solver()
    
    # Constraints
    s.add(T1 >= 540)  # Must leave GGP after 9:00 AM
    s.add(T2 >= T1 + 23)  # Travel time to Chinatown is 23 minutes
    
    # Calculate the start and end of the meeting window
    start_meeting = If(T1 + 23 >= 960, T1 + 23, 960)
    end_meeting = If(T2 <= 1305, T2, 1305)
    
    # Ensure meeting duration is at least 105 minutes
    s.add(end_meeting - start_meeting >= 105)
    
    if s.check() == sat:
        m = s.model()
        t1_val = m.eval(T1).as_long()
        t2_val = m.eval(T2).as_long()
        arr_val = t1_val + 23  # Arrival time at Chinatown
        
        # Helper function to convert minutes to time string
        def min_to_time(minutes):
            hours = minutes // 60
            mins = minutes % 60
            if hours >= 12:
                period = "PM"
                if hours > 12:
                    hours -= 12
            else:
                period = "AM"
                if hours == 0:
                    hours = 12
            return f"{hours}:{mins:02d} {period}"
        
        time_leave_ggp = min_to_time(t1_val)
        time_arrive_ct = min_to_time(arr_val)
        time_leave_ct = min_to_time(t2_val)
        
        # Output the schedule
        print("SOLUTION:")
        print(f"Leave Golden Gate Park at {time_leave_ggp}.")
        print(f"Arrive at Chinatown at {time_arrive_ct}.")
        print(f"Leave Chinatown at {time_leave_ct}.")
    else:
        print("No valid schedule found.")

if __name__ == "__main__":
    main()