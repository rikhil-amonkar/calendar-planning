from z3 import *

def min_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def main():
    # Initialize variables
    leave_NB = Int('leave_NB')
    start_emily = Int('start_emily')
    end_emily = Int('end_emily')
    start_margaret = Int('start_margaret')
    end_margaret = Int('end_margaret')
    
    s = Solver()
    
    # Convert time to minutes
    start_NB = 9 * 60  # 9:00 AM
    emily_avail_start = 16 * 60  # 16:00
    emily_avail_end = 17 * 60 + 15  # 17:15
    margaret_avail_start = 19 * 60  # 19:00
    margaret_avail_end = 21 * 60  # 21:00
    
    # Constraints
    s.add(leave_NB >= start_NB)
    s.add(start_emily == leave_NB + 7)  # Arrive exactly when meeting starts
    s.add(start_emily >= emily_avail_start)
    s.add(end_emily == start_emily + 45)  # Meet for exactly minimum 45 minutes
    s.add(end_emily <= emily_avail_end)
    
    s.add(start_margaret == end_emily + 13)  # Travel immediately after meeting
    s.add(start_margaret >= margaret_avail_start)
    s.add(end_margaret == start_margaret + 120)  # Meet for exactly 120 minutes
    s.add(end_margaret <= margaret_avail_end)
    
    if s.check() == sat:
        m = s.model()
        emily_start_val = m.eval(start_emily).as_long()
        emily_end_val = m.eval(end_emily).as_long()
        margaret_start_val = m.eval(start_margaret).as_long()
        margaret_end_val = m.eval(end_margaret).as_long()
        
        itinerary = [
            {"action": "meet", "person": "Emily", "start_time": min_to_time(emily_start_val), "end_time": min_to_time(emily_end_val)},
            {"action": "meet", "person": "Margaret", "start_time": min_to_time(margaret_start_val), "end_time": min_to_time(margaret_end_val)}
        ]
        result = {"itinerary": itinerary}
        print("SOLUTION:")
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()