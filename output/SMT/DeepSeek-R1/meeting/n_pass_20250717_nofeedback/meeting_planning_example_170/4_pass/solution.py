from z3 import *

def min_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

def main():
    # Convert times to minutes
    start_NB = 9 * 60  # 9:00 AM
    emily_avail_start = 16 * 60  # 16:00
    emily_avail_end = 17 * 60 + 15  # 17:15
    margaret_avail_start = 19 * 60  # 19:00
    margaret_avail_end = 21 * 60  # 21:00
    
    # Travel times in minutes
    NB_to_Emily = 7
    Emily_to_Margaret = 13
    Margaret_to_NB = 9
    
    # Declare variables
    leave_NB = Int('leave_NB')
    start_emily = Int('start_emily')
    end_emily = Int('end_emily')
    start_margaret = Int('start_margaret')
    end_margaret = Int('end_margaret')
    return_NB = Int('return_NB')
    
    s = Solver()
    
    # Constraints
    s.add(leave_NB >= start_NB)  # Can't leave NB before 9:00 AM
    
    # Emily meeting constraints
    s.add(start_emily == leave_NB + NB_to_Emily)
    s.add(start_emily >= emily_avail_start)
    s.add(end_emily == start_emily + 45)  # Exactly 45 minutes meeting
    s.add(end_emily <= emily_avail_end)
    
    # Travel to Margaret
    s.add(start_margaret == end_emily + Emily_to_Margaret)
    # Margaret meeting must start at or after her availability time
    s.add(start_margaret >= margaret_avail_start)
    s.add(end_margaret == start_margaret + 120)  # Exactly 120 minutes meeting
    s.add(end_margaret <= margaret_avail_end)
    
    # Return to NB
    s.add(return_NB == end_margaret + Margaret_to_NB)
    
    # Check and output
    if s.check() == sat:
        m = s.model()
        leave_NB_val = m.eval(leave_NB).as_long()
        start_emily_val = m.eval(start_emily).as_long()
        end_emily_val = m.eval(end_emily).as_long()
        start_margaret_val = m.eval(start_margaret).as_long()
        end_margaret_val = m.eval(end_margaret).as_long()
        return_NB_val = m.eval(return_NB).as_long()
        
        itinerary = [
            {
                "action": "meet",
                "person": "Emily",
                "start_time": min_to_time(start_emily_val),
                "end_time": min_to_time(end_emily_val)
            },
            {
                "action": "meet",
                "person": "Margaret",
                "start_time": min_to_time(start_margaret_val),
                "end_time": min_to_time(end_margaret_val)
            }
        ]
        result = {"itinerary": itinerary}
        print("SOLUTION:")
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()