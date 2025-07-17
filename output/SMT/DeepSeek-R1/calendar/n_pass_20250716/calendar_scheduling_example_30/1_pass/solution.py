from z3 import *

def main():
    # Define work hours and busy intervals in minutes from midnight
    work_start = 9 * 60  # 9:00 -> 540 minutes
    work_end = 17 * 60    # 17:00 -> 1020 minutes
    duration = 30         # Meeting duration in minutes

    # Jeffrey's busy intervals
    jeffrey_busy = [
        (9*60 + 30, 10*60),     # 9:30 to 10:00
        (10*60 + 30, 11*60)     # 10:30 to 11:00
    ]
    
    # Virginia's busy intervals
    virginia_busy = [
        (9*60, 9*60 + 30),      # 9:00 to 9:30
        (10*60, 10*60 + 30),    # 10:00 to 10:30
        (14*60 + 30, 15*60),    # 14:30 to 15:00
        (16*60, 16*60 + 30)     # 16:00 to 16:30
    ]
    
    # Melissa's busy intervals
    melissa_busy = [
        (9*60, 11*60 + 30),     # 9:00 to 11:30
        (12*60, 12*60 + 30),    # 12:00 to 12:30
        (13*60, 15*60),         # 13:00 to 15:00
        (16*60, 17*60)          # 16:00 to 17:00
    ]
    
    # Initialize Z3 solver and variable
    s = Solver()
    start = Int('start')
    
    # Constraint: meeting within work hours
    s.add(start >= work_start)
    s.add(start + duration <= work_end)
    
    # Add constraints for each participant's busy intervals
    for (busy_start, busy_end) in jeffrey_busy:
        s.add(Or(start >= busy_end, start + duration <= busy_start))
    
    for (busy_start, busy_end) in virginia_busy:
        s.add(Or(start >= busy_end, start + duration <= busy_start))
    
    for (busy_start, busy_end) in melissa_busy:
        s.add(Or(start >= busy_end, start + duration <= busy_start))
    
    # Try to satisfy Melissa's preference (end by 14:00)
    preference_end = 14 * 60  # 14:00 -> 840 minutes
    s.push()
    s.add(start + duration <= preference_end)
    
    if s.check() == sat:
        model = s.model()
        start_val = model[start].as_long()
    else:
        s.pop()
        if s.check() == sat:
            model = s.model()
            start_val = model[start].as_long()
        else:
            print("No solution found")
            return
    
    # Convert start and end times to HH:MM format
    start_hours = start_val // 60
    start_minutes = start_val % 60
    start_time = f"{start_hours}:{start_minutes:02d}"
    
    end_val = start_val + duration
    end_hours = end_val // 60
    end_minutes = end_val % 60
    end_time = f"{end_hours}:{end_minutes:02d}"
    
    print("Monday", start_time, end_time)

if __name__ == "__main__":
    main()