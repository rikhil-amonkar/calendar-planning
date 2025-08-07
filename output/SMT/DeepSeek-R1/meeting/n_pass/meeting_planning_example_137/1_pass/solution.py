from z3 import *

def main():
    # Define variables in minutes since midnight
    B1_start = Int('B1_start')
    B1_end = Int('B1_end')
    K_start = Int('K_start')
    K_end = Int('K_end')
    B2_start = Int('B2_start')
    B2_end = Int('B2_end')
    
    s = Solver()
    
    # Constraints
    s.add(B1_start >= 563)  # Arrive at GGP at 9:23 AM (540 + 23)
    s.add(B1_end >= B1_start + 45)  # Minimum 45 minutes with Barbara
    s.add(B1_end <= 787)  # Must leave GGP by 1:07 PM to meet Kenneth on time
    
    s.add(K_start >= B1_end + 23)  # Travel from GGP to CT takes 23 minutes
    s.add(K_start >= 720)  # Kenneth available from 12:00 PM
    s.add(K_end >= K_start + 90)  # Minimum 90 minutes with Kenneth
    s.add(K_end <= 900)  # Kenneth available until 3:00 PM
    
    s.add(B2_start == K_end + 23)  # Travel from CT to GGP takes 23 minutes
    s.add(B2_end >= B2_start + 45)  # Minimum 45 minutes with Barbara
    s.add(B2_end <= 1140)  # Barbara available until 7:00 PM
    
    if s.check() == sat:
        m = s.model()
        b1s = m.eval(B1_start).as_long()
        b1e = m.eval(B1_end).as_long()
        ks = m.eval(K_start).as_long()
        ke = m.eval(K_end).as_long()
        b2s = m.eval(B2_start).as_long()
        b2e = m.eval(B2_end).as_long()
        
        def min_to_time(minutes):
            h = minutes // 60
            m = minutes % 60
            return f"{h:02d}:{m:02d}"
        
        itinerary = [
            {"action": "meet", "person": "Barbara", "start_time": min_to_time(b1s), "end_time": min_to_time(b1e)},
            {"action": "meet", "person": "Kenneth", "start_time": min_to_time(ks), "end_time": min_to_time(ke)},
            {"action": "meet", "person": "Barbara", "start_time": min_to_time(b2s), "end_time": min_to_time(b2e)}
        ]
        
        result = {"itinerary": itinerary}
        print(f"SOLUTION: {result}")
    else:
        print("No feasible schedule found")

if __name__ == "__main__":
    main()