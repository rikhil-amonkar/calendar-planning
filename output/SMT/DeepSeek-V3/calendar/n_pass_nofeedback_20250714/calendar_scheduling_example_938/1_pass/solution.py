from z3 import *

def solve_scheduling():
    # Create the solver
    s = Solver()

    # Define the possible days (0=Monday, 1=Tuesday, ..., 4=Friday)
    day = Int('day')
    s.add(day >= 0, day <= 4)

    # Define the start time (in minutes from 9:00, so 0 = 9:00, 30 = 9:30, etc.)
    start_time = Int('start_time')
    # Working hours are 9:00 to 17:00 (480 minutes total, 8 hours)
    s.add(start_time >= 0, start_time <= 480 - 30)  # 30-minute meeting

    # Convert start_time to hours and minutes for readability
    start_hour = 9 + start_time // 60
    start_minute = start_time % 60

    # Define the end time (start_time + 30 minutes)
    end_time = start_time + 30
    end_hour = 9 + end_time // 60
    end_minute = end_time % 60

    # Ensure end time is within 17:00
    s.add(end_time <= 480)

    # Define the busy slots for Eugene and Eric
    # Eugene's busy slots (day, start_time, end_time in minutes from 9:00)
    eugene_busy = [
        (0, 2*60, 3*60),      # Monday 11:00-12:00
        (0, 4*60 + 30, 5*60),  # Monday 13:30-14:00
        (0, 5*60 + 30, 6*60),  # Monday 14:30-15:00
        (0, 7*60, 7*60 + 30),  # Monday 16:00-16:30
        (2, 0, 30),            # Wednesday 9:00-9:30
        (2, 2*60, 2*60 + 30),  # Wednesday 11:00-11:30
        (2, 3*60, 3*60 + 30),  # Wednesday 12:00-12:30
        (2, 4*60 + 30, 6*60),  # Wednesday 13:30-15:00
        (3, 30, 60),            # Thursday 9:30-10:00
        (3, 2*60, 3*60 + 30),   # Thursday 11:00-12:30
        (4, 1*60 + 30, 2*60),   # Friday 10:30-11:00
        (4, 3*60, 3*60 + 30),   # Friday 12:00-12:30
        (4, 4*60, 4*60 + 30),   # Friday 13:00-13:30
    ]

    # Eric's busy slots (day, start_time, end_time in minutes from 9:00)
    eric_busy = [
        (0, 0, 8*60),          # Monday 9:00-17:00
        (1, 0, 8*60),          # Tuesday 9:00-17:00
        (2, 0, 2*60 + 30),     # Wednesday 9:00-11:30
        (2, 3*60, 5*60),       # Wednesday 12:00-14:00
        (2, 5*60 + 30, 7*60 + 30),  # Wednesday 14:30-16:30
        (3, 0, 8*60),          # Thursday 9:00-17:00
        (4, 0, 2*60),          # Friday 9:00-11:00
        (4, 2*60 + 30, 8*60),  # Friday 11:30-17:00
    ]

    # Add constraints that the meeting does not overlap with any busy slot for Eugene
    for d, busy_start, busy_end in eugene_busy:
        s.add(Not(And(day == d,
                      Or(And(start_time < busy_end, end_time > busy_start)))))

    # Add constraints that the meeting does not overlap with any busy slot for Eric
    for d, busy_start, busy_end in eric_busy:
        s.add(Not(And(day == d,
                      Or(And(start_time < busy_end, end_time > busy_start)))))

    # Eric prefers to avoid Wednesday, so we add a soft constraint
    # Try to find a solution where day != 2 (Wednesday)
    # We'll first try without Wednesday, and if unsat, try with Wednesday
    temp_solver = Solver()
    temp_solver.add(s.assertions())
    temp_solver.add(day != 2)
    if temp_solver.check() == sat:
        s.add(day != 2)

    # Check if there's a solution
    if s.check() == sat:
        m = s.model()
        day_val = m[day].as_long()
        start_time_val = m[start_time].as_long()
        
        # Convert day_val to day name
        days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
        day_name = days[day_val]
        
        # Calculate start and end times
        start_hour = 9 + start_time_val // 60
        start_minute = start_time_val % 60
        end_time_val = start_time_val + 30
        end_hour = 9 + end_time_val // 60
        end_minute = end_time_val % 60
        
        # Format the output
        print("SOLUTION:")
        print(f"Day: {day_name}")
        print(f"Start Time: {start_hour:02d}:{start_minute:02d}")
        print(f"End Time: {end_hour:02d}:{end_minute:02d}")
    else:
        print("No solution found")

solve_scheduling()