from z3 import *

def main():
    s = Solver()
    day = Int('day')
    start_minutes = Int('start_minutes')
    
    # Constraints for day and start time
    s.add(day >= 0, day <= 3)  # 0: Mon, 1: Tue, 2: Wed, 3: Thu
    s.add(start_minutes >= 0, start_minutes <= 420)  # Meeting must end by 17:00 (480 minutes)
    
    # Define busy intervals in minutes (relative to 9:00)
    natalie_busy = {
        0: [(0, 30), (60, 180), (210, 240), (300, 330), (360, 450)],   # Monday
        1: [(0, 30), (60, 90), (210, 300), (420, 480)],                # Tuesday
        2: [(120, 150), (420, 450)],                                   # Wednesday
        3: [(60, 120), (150, 360), (390, 420), (450, 480)]             # Thursday
    }
    
    william_busy = {
        0: [(30, 120), (150, 480)],                                    # Monday
        1: [(0, 240), (270, 420)],                                     # Tuesday
        2: [(0, 210), (240, 330), (390, 420), (450, 480)],             # Wednesday
        3: [(0, 90), (120, 150), (180, 210), (240, 300), (360, 480)]   # Thursday
    }
    
    # Add constraints for each day
    for d in range(4):
        natalie_cons = []
        for s_busy, e_busy in natalie_busy[d]:
            natalie_cons.append(Or(start_minutes + 60 <= s_busy, start_minutes >= e_busy))
        
        william_cons = []
        for s_busy, e_busy in william_busy[d]:
            william_cons.append(Or(start_minutes + 60 <= s_busy, start_minutes >= e_busy))
        
        # Combine constraints for both participants
        all_cons = natalie_cons + william_cons
        s.add(If(day == d, And(all_cons), True))
    
    # Check for solution
    if s.check() == sat:
        m = s.model()
        d_val = m[day].as_long()
        start_val = m[start_minutes].as_long()
        
        # Convert start time to HH:MM
        hours = 9 + start_val // 60
        minutes = start_val % 60
        start_time = f"{hours}:{minutes:02d}"
        
        # Calculate end time
        end_val = start_val + 60
        end_hours = 9 + end_val // 60
        end_minutes = end_val % 60
        end_time = f"{end_hours}:{end_minutes:02d}"
        
        # Map day value to string
        days = ["Monday", "Tuesday", "Wednesday", "Thursday"]
        day_str = days[d_val]
        
        print(f"Schedule the meeting on {day_str} from {start_time} to {end_time}.")
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()