from z3 import *

def solve_meeting_schedule():
    # Create the solver
    s = Solver()
    
    # Define variables
    day = Int('day')  # 0: Monday, 1: Tuesday, 2: Wednesday, 3: Thursday
    start_time = Int('start_time')  # in minutes from 9:00 (e.g., 0 is 9:00, 60 is 10:00)
    
    # Constraints for day: must be 0, 1, or 3 (Mon, Tue, Thu), excluding Wednesday (2)
    s.add(Or(day == 0, day == 1, day == 3))
    
    # Meeting duration is 60 minutes (1 hour)
    duration = 60
    # Work hours are 9:00 to 17:00 (8 hours, 480 minutes)
    # So start_time must be >= 0 and <= 480 - duration (420)
    s.add(start_time >= 0)
    s.add(start_time <= 420)  # 17:00 - 1 hour = 16:00 start (420 minutes from 9:00 is 16:00)
    
    # Laura's busy times per day, each is (day, start, end) in minutes from 9:00
    laura_busy = [
        # Monday (day 0)
        (0, 90, 120),   # 10:30-11:00 (90 to 120 minutes)
        (0, 210, 240),  # 12:30-13:00
        (0, 330, 390),  # 14:30-15:30
        (0, 420, 480),  # 16:00-17:00
        # Tuesday (day 1)
        (1, 30, 60),    # 9:30-10:00
        (1, 120, 150),  # 11:00-11:30
        (1, 240, 270),  # 13:00-13:30
        (1, 330, 360),  # 14:30-15:00
        (1, 420, 480),  # 16:00-17:00
        # Wednesday (day 2) - excluded, but included for completeness
        (2, 150, 180),  # 11:30-12:00
        (2, 210, 240),  # 12:30-13:00
        (2, 390, 450),  # 15:30-16:30
        # Thursday (day 3)
        (3, 90, 120),   # 10:30-11:00
        (3, 180, 270),  # 12:00-13:30
        (3, 360, 390),  # 15:00-15:30
        (3, 420, 450),  # 16:00-16:30
    ]
    
    # Philip's busy times per day (day, start, end) in minutes from 9:00
    philip_busy = [
        # Monday (day 0)
        (0, 0, 480),  # 9:00-17:00 (entire day)
        # Tuesday (day 1)
        (1, 0, 120),  # 9:00-11:00
        (1, 150, 180),  # 11:30-12:00
        (1, 240, 270),  # 13:00-13:30
        (1, 300, 330),  # 14:00-14:30
        (1, 360, 450),  # 15:00-16:30
        # Wednesday (day 2) - excluded
        (2, 0, 60),    # 9:00-10:00
        (2, 120, 180), # 11:00-12:00
        (2, 210, 420), # 12:30-16:00
        (2, 450, 480), # 16:30-17:00
        # Thursday (day 3)
        (3, 0, 90),    # 9:00-10:30
        (3, 120, 210),  # 11:00-12:30
        (3, 240, 480),  # 13:00-17:00
    ]
    
    # For the selected day, the meeting must not overlap with any busy times of Laura or Philip
    def add_busy_constraints(busy_times):
        for d, busy_start, busy_end in busy_times:
            s.add(Not(And(day == d,
                          Or(
                              And(start_time >= busy_start, start_time < busy_end),
                              And(start_time + duration > busy_start, start_time + duration <= busy_end),
                              And(start_time <= busy_start, start_time + duration >= busy_end)
                          )))
    
    add_busy_constraints(laura_busy)
    add_busy_constraints(philip_busy)
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        solved_day = m[day].as_long()
        solved_start = m[start_time].as_long()
        
        # Convert day to name
        days = ["Monday", "Tuesday", "Wednesday", "Thursday"]
        day_name = days[solved_day]
        
        # Convert start time to HH:MM
        start_hour = 9 + solved_start // 60
        start_minute = solved_start % 60
        start_time_str = f"{start_hour:02d}:{start_minute:02d}"
        
        # Calculate end time
        end_time_min = solved_start + duration
        end_hour = 9 + end_time_min // 60
        end_minute = end_time_min % 60
        end_time_str = f"{end_hour:02d}:{end_minute:02d}"
        
        # Print the solution
        print("SOLUTION:")
        print(f"Day: {day_name}")
        print(f"Start Time: {start_time_str}")
        print(f"End Time: {end_time_str}")
    else:
        print("No solution found")

solve_meeting_schedule()