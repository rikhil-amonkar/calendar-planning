from z3 import *

def main():
    day = "Monday"
    work_start_minutes = 0
    work_end_minutes = 480
    meeting_duration = 60
    
    s = Solver()
    start = Int('start')
    
    s.add(start >= work_start_minutes)
    s.add(start + meeting_duration <= work_end_minutes)
    
    james_busy = [(150, 180), (330, 360)]
    john_busy = [(30, 120), (150, 180), (210, 270), (330, 450)]
    
    for (busy_start, busy_end) in james_busy:
        s.add(Or(start + meeting_duration <= busy_start, start >= busy_end))
    
    for (busy_start, busy_end) in john_busy:
        s.add(Or(start + meeting_duration <= busy_start, start >= busy_end))
    
    if s.check() == sat:
        m = s.model()
        start_val = m.eval(start).as_long()
        
        total_minutes = start_val
        hours = 9 + total_minutes // 60
        minutes = total_minutes % 60
        start_time = f"{hours}:{minutes:02d}"
        
        end_minutes = start_val + meeting_duration
        end_hours = 9 + end_minutes // 60
        end_minutes_remainder = end_minutes % 60
        end_time = f"{end_hours}:{end_minutes_remainder:02d}"
        
        print(f"Day: {day}")
        print(f"Start Time: {start_time}")
        print(f"End Time: {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()