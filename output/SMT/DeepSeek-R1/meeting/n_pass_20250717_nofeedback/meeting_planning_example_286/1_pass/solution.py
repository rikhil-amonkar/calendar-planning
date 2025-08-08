from z3 import *
import json

def main():
    sC = Int('sC')
    sR = Int('sR')
    sK = Int('sK')
    
    # Common constraints for each friend's availability and minimum meeting duration
    constraints_common = [
        sC >= 75, sC <= 135,  # Carol: 75 (10:15 AM) to 135 (11:15 AM) to end by 165 (11:45 AM)
        sR >= 150, sR <= 555,  # Rebecca: 150 (11:30 AM) to 555 (5:15 PM) to end by 675 (8:15 PM)
        sK >= 225, sK <= 240   # Karen: 225 (12:45 PM) to 240 (1:00 PM) to end by 360 (3:00 PM)
    ]
    
    # Define constraints for each possible meeting order
    order1 = And(  # Carol -> Rebecca -> Karen
        sC >= 26,  # Travel from Union Square to Sunset District: 26 min
        sR >= sC + 30 + 24,  # Travel from Sunset District to Mission District: 24 min
        sK >= sR + 120 + 15   # Travel from Mission District to Bayview: 15 min
    )
    
    order2 = And(  # Carol -> Karen -> Rebecca
        sC >= 26,
        sK >= sC + 30 + 22,  # Travel from Sunset District to Bayview: 22 min
        sR >= sK + 120 + 13  # Travel from Bayview to Mission District: 13 min
    )
    
    order3 = And(  # Rebecca -> Carol -> Karen
        sR >= 14,  # Travel from Union Square to Mission District: 14 min
        sC >= sR + 120 + 24,  # Travel from Mission District to Sunset District: 24 min
        sK >= sC + 30 + 22    # Travel from Sunset District to Bayview: 22 min
    )
    
    order4 = And(  # Rebecca -> Karen -> Carol
        sR >= 14,
        sK >= sR + 120 + 15,  # Travel from Mission District to Bayview: 15 min
        sC >= sK + 120 + 23   # Travel from Bayview to Sunset District: 23 min
    )
    
    order5 = And(  # Karen -> Carol -> Rebecca
        sK >= 15,  # Travel from Union Square to Bayview: 15 min
        sC >= sK + 120 + 23,  # Travel from Bayview to Sunset District: 23 min
        sR >= sC + 30 + 24    # Travel from Sunset District to Mission District: 24 min
    )
    
    order6 = And(  # Karen -> Rebecca -> Carol
        sK >= 15,
        sR >= sK + 120 + 13,  # Travel from Bayview to Mission District: 13 min
        sC >= sR + 120 + 24   # Travel from Mission District to Sunset District: 24 min
    )
    
    # Combine all constraints
    s = Solver()
    s.add(constraints_common)
    s.add(Or(order1, order2, order3, order4, order5, order6))
    
    if s.check() == sat:
        m = s.model()
        sC_val = m[sC].as_long()
        sR_val = m[sR].as_long()
        sK_val = m[sK].as_long()
        
        # Convert minutes to time strings (in 24-hour format)
        def minutes_to_time(minutes):
            total_minutes = 9 * 60 + minutes
            h = total_minutes // 60
            m = total_minutes % 60
            return f"{h:02d}:{m:02d}"
        
        # Create meeting entries
        meetings = [
            {"person": "Carol", "start": sC_val, "end": sC_val + 30, "start_time": minutes_to_time(sC_val), "end_time": minutes_to_time(sC_val + 30)},
            {"person": "Rebecca", "start": sR_val, "end": sR_val + 120, "start_time": minutes_to_time(sR_val), "end_time": minutes_to_time(sR_val + 120)},
            {"person": "Karen", "start": sK_val, "end": sK_val + 120, "start_time": minutes_to_time(sK_val), "end_time": minutes_to_time(sK_val + 120)}
        ]
        
        # Sort meetings by start time
        meetings_sorted = sorted(meetings, key=lambda x: x["start"])
        itinerary = [{"action": "meet", "person": m["person"], "start_time": m["start_time"], "end_time": m["end_time"]} for m in meetings_sorted]
        
        # Output the solution in JSON format
        result = {"itinerary": itinerary}
        print("SOLUTION:")
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()