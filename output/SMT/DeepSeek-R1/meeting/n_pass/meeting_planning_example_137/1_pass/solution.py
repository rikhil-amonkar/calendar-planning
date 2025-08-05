from z3 import *
import json

def main():
    s = Solver()
    
    # Define variables
    order = Bool('order')
    B_start = Int('B_start')
    B_end = Int('B_end')
    K_start = Int('K_start')
    K_end = Int('K_end')
    
    # Times in minutes since midnight
    start = 540   # 9:00
    k_start_avail = 720  # 12:00
    k_end_avail = 900    # 15:00
    b_start_avail = 495  # 8:15
    b_end_avail = 1140   # 19:00
    
    # Travel times
    FD_GGP = 23
    FD_Chinatown = 5
    GGP_Chinatown = 23
    Chinatown_GGP = 23
    
    # Common constraints for Barbara
    s.add(B_start >= b_start_avail)
    s.add(B_end <= b_end_avail)
    s.add(B_end - B_start >= 45)
    
    # Common constraints for Kenneth
    s.add(K_start >= k_start_avail)
    s.add(K_end <= k_end_avail)
    s.add(K_end - K_start >= 90)
    s.add(K_start <= 810)  # Kenneth must start by 13:30 to have 90 minutes by 15:00
    
    # Order constraints: Barbara first or Kenneth first
    s.add(Implies(order, 
                 And(
                     B_start >= start + FD_GGP,          # Arrive at Barbara by 9:23
                     K_start >= B_end + GGP_Chinatown    # Travel from Barbara to Kenneth takes 23 min
                 )))
    s.add(Implies(Not(order),
                 And(
                     K_start >= start + FD_Chinatown,    # Arrive at Kenneth by 9:05
                     B_start >= K_end + Chinatown_GGP     # Travel from Kenneth to Barbara takes 23 min
                 )))
    
    if s.check() == sat:
        m = s.model()
        
        # Extract values
        B_start_val = m[B_start].as_long()
        B_end_val = m[B_end].as_long()
        K_start_val = m[K_start].as_long()
        K_end_val = m[K_end].as_long()
        
        # Helper function to convert minutes to HH:MM
        def min_to_time(mins):
            hours, minutes = divmod(mins, 60)
            return f"{hours:02d}:{minutes:02d}"
        
        # Create meeting events
        barbara_meeting = {
            "action": "meet",
            "person": "Barbara",
            "start_time": min_to_time(B_start_val),
            "end_time": min_to_time(B_end_val)
        }
        kenneth_meeting = {
            "action": "meet",
            "person": "Kenneth",
            "start_time": min_to_time(K_start_val),
            "end_time": min_to_time(K_end_val)
        }
        
        # Sort meetings by start time
        itinerary = [barbara_meeting, kenneth_meeting]
        sorted_itinerary = sorted(itinerary, key=lambda x: x['start_time'])
        
        # Output as JSON
        result = {"itinerary": sorted_itinerary}
        print(json.dumps(result))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()