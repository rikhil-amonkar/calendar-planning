from z3 import *
import json

def min_to_time(minutes):
    total_minutes = minutes
    hours = 9 + total_minutes // 60
    mins = total_minutes % 60
    return f"{hours:02d}:{mins:02d}"

def main():
    T0 = Int('T0')
    J_start = Int('J_start')
    R_start = Int('R_start')
    order = Int('order')
    
    s = Solver()
    
    # James: available from 12:45 (225 minutes from 9:00) to 14:00 (300 minutes)
    s.add(J_start >= 225)
    s.add(J_start + 75 <= 300)  # Meeting duration 75 minutes
    
    # Robert: available from 12:45 (225 minutes) to 15:15 (375 minutes)
    s.add(R_start >= 225)
    s.add(R_start + 30 <= 375)  # Meeting duration 30 minutes
    
    # Order: 0 for James first, 1 for Robert first
    s.add(Or(order == 0, order == 1))
    
    # Travel constraints based on order
    s.add(If(order == 0,
             And(T0 + 18 <= J_start,  # North Beach to Mission District: 18 min
                 J_start + 75 + 7 <= R_start),  # Mission District to The Castro: 7 min
             And(T0 + 22 <= R_start,  # North Beach to The Castro: 22 min
                 R_start + 30 + 7 <= J_start)))  # The Castro to Mission District: 7 min
    
    s.add(T0 >= 0)  # Cannot leave before 9:00 AM
    
    if s.check() == sat:
        m = s.model()
        J_start_val = m[J_start].as_long()
        R_start_val = m[R_start].as_long()
        
        # Format meeting times
        meeting_james = {
            "action": "meet",
            "person": "James",
            "start_time": min_to_time(J_start_val),
            "end_time": min_to_time(J_start_val + 75)
        }
        meeting_robert = {
            "action": "meet",
            "person": "Robert",
            "start_time": min_to_time(R_start_val),
            "end_time": min_to_time(R_start_val + 30)
        }
        
        # Sort meetings by start time
        meetings = [
            (J_start_val, meeting_james),
            (R_start_val, meeting_robert)
        ]
        meetings_sorted = sorted(meetings, key=lambda x: x[0])
        itinerary = [meeting[1] for meeting in meetings_sorted]
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        # Fallback if no solution found (though our constraints ensure a solution exists)
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()