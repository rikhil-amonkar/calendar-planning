from z3 import *
import json

def main():
    # Initialize variables for start times and positions
    C_start = Int('C_start')  # Carol's start time in minutes from midnight
    K_start = Int('K_start')  # Karen's start time
    R_start = Int('R_start')  # Rebecca's start time
    pos_C = Int('pos_C')      # Position of Carol's meeting (0,1,2)
    pos_K = Int('pos_K')      # Position of Karen's meeting
    pos_R = Int('pos_R')      # Position of Rebecca's meeting
    
    s = Solver()
    
    # Define position constraints: each position is 0, 1, or 2 and all distinct
    s.add(pos_C >= 0, pos_C <= 2)
    s.add(pos_K >= 0, pos_K <= 2)
    s.add(pos_R >= 0, pos_R <= 2)
    s.add(Distinct(pos_C, pos_K, pos_R))
    
    # Time window constraints in minutes
    # Carol: 10:15 AM (615 minutes) to 11:45 AM (705 minutes)
    s.add(C_start >= 615, C_start + 30 <= 705)
    # Karen: 12:45 PM (765 minutes) to 3:00 PM (900 minutes)
    s.add(K_start >= 765, K_start + 120 <= 900)
    # Rebecca: 11:30 AM (690 minutes) to 8:15 PM (1215 minutes)
    s.add(R_start >= 690, R_start + 120 <= 1215)
    
    # First meeting must account for travel from Union Square (starting at 540 minutes = 9:00 AM)
    s.add(Or(
        And(pos_C == 0, C_start >= 540 + 26),  # Travel to Sunset: 26 minutes
        And(pos_K == 0, K_start >= 540 + 15),  # Travel to Bayview: 15 minutes
        And(pos_R == 0, R_start >= 540 + 14)   # Travel to Mission: 14 minutes
    ))
    
    # Define travel times between locations
    # Carol: Sunset (SD), Karen: Bayview (BV), Rebecca: Mission (MD)
    # Constraints for consecutive meetings
    # Carol -> Karen: SD to BV takes 22 minutes
    s.add(If(pos_K == pos_C + 1, C_start + 30 + 22 <= K_start, True))
    # Karen -> Carol: BV to SD takes 23 minutes
    s.add(If(pos_C == pos_K + 1, K_start + 120 + 23 <= C_start, True))
    
    # Carol -> Rebecca: SD to MD takes 24 minutes
    s.add(If(pos_R == pos_C + 1, C_start + 30 + 24 <= R_start, True))
    # Rebecca -> Carol: MD to SD takes 24 minutes
    s.add(If(pos_C == pos_R + 1, R_start + 120 + 24 <= C_start, True))
    
    # Karen -> Rebecca: BV to MD takes 13 minutes
    s.add(If(pos_R == pos_K + 1, K_start + 120 + 13 <= R_start, True))
    # Rebecca -> Karen: MD to BV takes 15 minutes
    s.add(If(pos_K == pos_R + 1, R_start + 120 + 15 <= K_start, True))
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        # Extract start times
        c_val = m.eval(C_start).as_long()
        k_val = m.eval(K_start).as_long()
        r_val = m.eval(R_start).as_long()
        
        # Create meeting entries
        meetings = [
            {"person": "Carol", "start": c_val, "end": c_val + 30},
            {"person": "Karen", "start": k_val, "end": k_val + 120},
            {"person": "Rebecca", "start": r_val, "end": r_val + 120}
        ]
        
        # Sort meetings by start time
        meetings.sort(key=lambda x: x["start"])
        
        # Format times to HH:MM
        def format_time(minutes):
            h = minutes // 60
            m = minutes % 60
            return f"{h:02d}:{m:02d}"
        
        itinerary = []
        for meet in meetings:
            itinerary.append({
                "action": "meet",
                "person": meet["person"],
                "start_time": format_time(meet["start"]),
                "end_time": format_time(meet["end"])
            })
        
        # Output the solution in JSON format
        result = {"itinerary": itinerary}
        print("SOLUTION:")
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()