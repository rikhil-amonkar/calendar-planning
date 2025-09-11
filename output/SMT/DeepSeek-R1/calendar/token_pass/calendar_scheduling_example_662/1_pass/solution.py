from z3 import *

def main():
    # Initialize solver
    s = Solver()
    
    # Define variables: day (0=Monday, 1=Tuesday) and start time in minutes from 9:00
    day = Int('day')
    start = Int('start')
    
    # Meeting duration in minutes
    duration = 60
    
    # Total available minutes per day (9:00 to 17:00 is 8 hours = 480 minutes)
    total_minutes = 480
    
    # Constrain day to Monday (0) or Tuesday (1)
    s.add(Or(day == 0, day == 1))
    
    # Constrain start time to be within available hours (0 to 480 - duration)
    s.add(start >= 0, start <= total_minutes - duration)
    
    # Define blocked times in minutes from 9:00
    gary_monday = [(30, 60), (120, 240), (300, 330), (450, 480)]
    gary_tuesday = [(0, 30), (90, 120), (330, 420)]
    
    david_monday = [(0, 30), (60, 240), (330, 450)]
    david_tuesday = [(0, 30), (60, 90), (120, 210), (240, 330), (360, 420), (450, 480)]
    
    # Function to check non-overlap with blocked intervals
    def no_overlap(blocks, s_time):
        return And([Or(s_time + duration <= block_start, s_time >= block_end) for (block_start, block_end) in blocks])
    
    # Add constraints based on selected day
    s.add(If(day == 0, 
             And(no_overlap(gary_monday, start), no_overlap(david_monday, start)), 
             True))
    s.add(If(day == 1,
             And(no_overlap(gary_tuesday, start), no_overlap(david_tuesday, start)),
             True))
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        d = m[day].as_long()
        s_val = m[start].as_long()
        
        # Convert start time to HH:MM format
        start_hour = 9 + s_val // 60
        start_minute = s_val % 60
        end_time = s_val + duration
        end_hour = 9 + end_time // 60
        end_minute = end_time % 60
        
        day_str = "Monday" if d == 0 else "Tuesday"
        print(f"{day_str} {start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()