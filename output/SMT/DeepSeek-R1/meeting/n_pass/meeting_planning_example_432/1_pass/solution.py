from z3 import *

def min_to_time(total_minutes):
    hours = 9 + total_minutes // 60
    minutes = total_minutes % 60
    if hours < 12:
        return f"{hours}:{minutes:02d} AM"
    elif hours == 12:
        return f"12:{minutes:02d} PM"
    else:
        return f"{hours - 12}:{minutes:02d} PM"

def main():
    # Create integer variables for start times of each meeting
    s0 = Int('s0')  # Joseph (Fisherman's Wharf)
    s1 = Int('s1')  # Jeffrey (Bayview)
    s2 = Int('s2')  # Kevin (Mission District)
    s3 = Int('s3')  # Barbara (Financial District)
    
    solver = Solver()
    
    # Kevin at Mission District: available from 135 to 345 minutes (11:15 AM to 3:15 PM)
    solver.add(s2 >= 135, s2 <= 345)
    
    # Barbara at Financial District: after Kevin (travel time 17 minutes) and available from 90 to 435 minutes
    solver.add(s3 >= s2 + 30 + 17, s3 >= 90, s3 <= 435)
    
    # Joseph at Fisherman's Wharf: after Barbara (travel time 10 minutes) and available from 24 to 420 minutes
    solver.add(s0 >= s3 + 15 + 10, s0 >= 24, s0 <= 420)
    
    # Jeffrey at Bayview: after Joseph (travel time 26 minutes) and available from 510 to 690 minutes
    solver.add(s1 >= s0 + 90 + 26, s1 >= 510, s1 <= 690)
    
    if solver.check() == sat:
        model = solver.model()
        s2_val = model[s2].as_long()
        s3_val = model[s3].as_long()
        s0_val = model[s0].as_long()
        s1_val = model[s1].as_long()
        
        # Print the schedule
        print("SOLUTION:")
        print(f"Kevin at Mission District: {min_to_time(s2_val)} to {min_to_time(s2_val + 30)}")
        print(f"Barbara at Financial District: {min_to_time(s3_val)} to {min_to_time(s3_val + 15)}")
        print(f"Joseph at Fisherman's Wharf: {min_to_time(s0_val)} to {min_to_time(s0_val + 90)}")
        print(f"Jeffrey at Bayview: {min_to_time(s1_val)} to {min_to_time(s1_val + 60)}")
    else:
        print("No feasible schedule found.")

if __name__ == "__main__":
    main()