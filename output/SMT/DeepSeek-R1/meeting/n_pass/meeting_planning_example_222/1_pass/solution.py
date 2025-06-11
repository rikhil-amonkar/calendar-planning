from z3 import *

def main():
    # Define integer variables for start times in minutes from 9:00 AM
    H_start = Int('H_start')
    K_start = Int('K_start')
    P_start = Int('P_start')
    
    s = Solver()
    
    # Helen's constraints (North Beach)
    s.add(H_start >= 8)  # Travel from Nob Hill to North Beach: 8 minutes
    s.add(H_start + 120 <= 465)  # Helen available until 4:45 PM (465 minutes)
    
    # Kimberly's constraints (Fisherman's Wharf)
    s.add(K_start >= 450)  # Kimberly available from 4:30 PM (450 minutes)
    s.add(K_start + 45 <= 720)  # Kimberly available until 9:00 PM (720 minutes)
    
    # Patricia's constraints (Bayview)
    s.add(P_start >= 540)  # Patricia available from 6:00 PM (540 minutes)
    s.add(P_start + 120 <= 735)  # Patricia available until 9:15 PM (735 minutes)
    
    # Travel constraints between meetings
    s.add(H_start + 120 + 5 <= K_start)  # Travel from North Beach to Fisherman's Wharf: 5 minutes
    s.add(K_start + 45 + 26 <= P_start)  # Travel from Fisherman's Wharf to Bayview: 26 minutes
    
    # Check for a feasible schedule
    if s.check() == sat:
        m = s.model()
        h_val = m.eval(H_start).as_long()
        k_val = m.eval(K_start).as_long()
        p_val = m.eval(P_start).as_long()
        
        # Convert minutes to time string (24-hour format)
        def to_time(minutes):
            total_minutes = minutes
            hours = total_minutes // 60
            mins = total_minutes % 60
            total_hours = 9 + hours
            return f"{total_hours}:{mins:02d}"
        
        # Calculate meeting end times
        h_end_val = h_val + 120
        k_end_val = k_val + 45
        p_end_val = p_val + 120
        
        # Convert to time strings
        h_start_time = to_time(h_val)
        h_end_time = to_time(h_end_val)
        k_start_time = to_time(k_val)
        k_end_time = to_time(k_end_val)
        p_start_time = to_time(p_val)
        p_end_time = to_time(p_end_val)
        
        # Output the schedule
        print("SOLUTION:")
        print(f"Meeting with Helen at North Beach: from {h_start_time} to {h_end_time}")
        print(f"Travel from North Beach to Fisherman's Wharf: 5 minutes")
        print(f"Meeting with Kimberly at Fisherman's Wharf: from {k_start_time} to {k_end_time}")
        print(f"Travel from Fisherman's Wharf to Bayview: 26 minutes")
        print(f"Meeting with Patricia at Bayview: from {p_start_time} to {p_end_time}")
    else:
        print("No feasible schedule found to meet all three friends.")

if __name__ == "__main__":
    main()