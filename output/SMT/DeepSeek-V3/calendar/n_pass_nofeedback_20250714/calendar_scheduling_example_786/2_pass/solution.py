from z3 import *

def solve_meeting_schedule():
    # Create the solver
    s = Solver()
    
    # Define variables
    day = Int('day')  # 0: Monday, 1: Tuesday, 2: Wednesday
    start_time = Int('start_time')  # in minutes from 9:00 (e.g., 0 is 9:00, 60 is 10:00)
    
    # Meeting duration is 30 minutes
    duration = 30
    end_time = start_time + duration
    
    # Possible days: Monday (0), Tuesday (1), Wednesday (2)
    s.add(day >= 0, day <= 2)
    
    # Meeting must be within 9:00-17:00 (work hours)
    s.add(start_time >= 0, end_time <= 8 * 60)  # 8 hours from 9:00 to 17:00 is 8*60 minutes
    
    # Amy's busy times per day (in minutes from 9:00)
    amy_busy = {
        0: [],  # Monday: no busy times
        1: [],   # Tuesday: no busy times
        2: [(120, 150), (270, 300)]  # Wednesday: 11:00-11:30 (120-150), 13:30-14:00 (270-300)
    }
    
    # Pamela's busy times per day (in minutes from 9:00)
    pamela_busy = {
        0: [(0, 90), (120, 450)],  # Monday: 9:00-10:30 (0-90), 11:00-16:30 (120-450)
        1: [(0, 30), (60, 480)],   # Tuesday: 9:00-9:30 (0-30), 10:00-17:00 (60-480)
        2: [(0, 30), (60, 120), (150, 270), (330, 360), (420, 450)]  # Wednesday: 9:00-9:30 (0-30), 10:00-11:00 (60-120), 11:30-13:30 (150-270), 14:30-15:00 (330-360), 16:00-16:30 (420-450)
    }
    
    # Constraints for each possible day
    for d in [0, 1, 2]:
        # If the meeting is on day d, then it must not overlap with Amy's and Pamela's busy times
        s.add(Implies(day == d, And(
            # Check Amy's busy times
            Not(Or([And(start_time < busy_end, end_time > busy_start) for (busy_start, busy_end) in amy_busy[d]])),
            # Check Pamela's busy times
            Not(Or([And(start_time < busy_end, end_time > busy_start) for (busy_start, busy_end) in pamela_busy[d]]))
        )))
    
    # Pamela's preferences: avoid Monday and before 16:00 on Tuesday and Wednesday
    s.add(Not(day == 0))  # not Monday
    s.add(Or(
        day == 1,  # Tuesday: must be after 16:00 (420 minutes from 9:00)
        And(day == 2, start_time >= 420)  # Wednesday: must start at or after 16:00
    ))
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        day_val = m[day].as_long()
        start_min = m[start_time].as_long()
        
        # Convert day_val to day name
        days = ["Monday", "Tuesday", "Wednesday"]
        day_name = days[day_val]
        
        # Convert start_min to HH:MM
        start_hour = 9 + start_min // 60
        start_minute = start_min % 60
        start_time_str = f"{start_hour:02d}:{start_minute:02d}"
        
        # Calculate end time
        end_min = start_min + duration
        end_hour = 9 + end_min // 60
        end_minute = end_min % 60
        end_time_str = f"{end_hour:02d}:{end_minute:02d}"
        
        # Print the solution
        print("SOLUTION:")
        print(f"Day: {day_name}")
        print(f"Start Time: {start_time_str}")
        print(f"End Time: {end_time_str}")
    else:
        print("No solution found")

solve_meeting_schedule()