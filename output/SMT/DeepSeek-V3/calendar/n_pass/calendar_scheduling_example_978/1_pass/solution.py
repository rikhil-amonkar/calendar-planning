from z3 import *

def solve_meeting_scheduling():
    # Initialize the solver
    s = Solver()
    
    # Define the variables
    day = Int('day')  # 0: Monday, 1: Tuesday, 2: Wednesday, 3: Thursday, 4: Friday
    start_time = Int('start_time')  # in minutes from 9:00 (e.g., 0 = 9:00, 60 = 10:00)
    
    # Meeting duration is 1 hour (60 minutes)
    duration = 60
    
    # Constraints for day: must be between 0 (Monday) and 4 (Friday)
    s.add(day >= 0, day <= 4)
    
    # Constraints for start_time: must be between 0 (9:00) and 480 (17:00 - duration)
    s.add(start_time >= 0, start_time <= 480 - duration)
    
    # Define the busy times for Brian and Julia for each day
    # Each entry is (day, start_min, end_min)
    # Convert HH:MM to minutes since 9:00. For example, 10:30 is 90 minutes (60 + 30)
    
    # Brian's busy times
    brian_busy = [
        (0, 30, 60),    # Monday 9:30-10:00
        (0, 210, 330),   # Monday 12:30-14:30
        (0, 390, 420),   # Monday 15:30-16:00
        (1, 0, 30),      # Tuesday 9:00-9:30
        (2, 210, 300),   # Wednesday 12:30-14:00
        (2, 450, 480),   # Wednesday 16:30-17:00
        (3, 120, 150),   # Thursday 11:00-11:30
        (3, 240, 270),   # Thursday 13:00-13:30
        (3, 450, 480),   # Thursday 16:30-17:00
        (4, 30, 60),     # Friday 9:30-10:00
        (4, 90, 120),    # Friday 10:30-11:00
        (4, 240, 270),   # Friday 13:00-13:30
        (4, 360, 420),    # Friday 15:00-16:00
        (4, 450, 480)     # Friday 16:30-17:00
    ]
    
    # Julia's busy times
    julia_busy = [
        (0, 0, 60),      # Monday 9:00-10:00
        (0, 120, 150),    # Monday 11:00-11:30
        (0, 210, 240),    # Monday 12:30-13:00
        (0, 390, 420),    # Monday 15:30-16:00
        (1, 240, 300),    # Tuesday 13:00-14:00
        (1, 420, 450),    # Tuesday 16:00-16:30
        (2, 0, 150),      # Wednesday 9:00-11:30
        (2, 180, 210),    # Wednesday 12:00-12:30
        (2, 240, 480),    # Wednesday 13:00-17:00
        (3, 0, 90),       # Thursday 9:00-10:30
        (3, 120, 480),    # Thursday 11:00-17:00
        (4, 0, 60),       # Friday 9:00-10:00
        (4, 90, 150),     # Friday 10:30-11:30
        (4, 210, 300),    # Friday 12:30-14:00
        (4, 330, 360),    # Friday 14:30-15:00
        (4, 390, 420)     # Friday 15:30-16:00
    ]
    
    # Function to check if the meeting overlaps with any busy interval
    def no_overlap(d, st, busy_intervals):
        constraints = []
        for (busy_day, busy_start, busy_end) in busy_intervals:
            # If the day matches, then the meeting should not overlap
            constraint = Or(
                d != busy_day,
                st >= busy_end,
                st + duration <= busy_start
            )
            constraints.append(constraint)
        return And(*constraints)
    
    # Add constraints for Brian and Julia's busy times
    s.add(no_overlap(day, start_time, brian_busy))
    s.add(no_overlap(day, start_time, julia_busy))
    
    # Brian prefers to avoid Monday (day 0), so we first try to find a solution where day != 0
    # If no solution, then we allow Monday
    temp_solver = Solver()
    temp_solver.add(s.assertions())
    temp_solver.add(day != 0)
    
    solution = None
    if temp_solver.check() == sat:
        model = temp_solver.model()
        solution = (model[day].as_long(), model[start_time].as_long())
    else:
        # Check with Monday allowed
        if s.check() == sat:
            model = s.model()
            solution = (model[day].as_long(), model[start_time].as_long())
    
    if not solution:
        print("No solution found")
        return
    
    day_num, start_min = solution
    days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
    selected_day = days[day_num]
    
    # Convert start_min to HH:MM
    total_min = 9 * 60 + start_min
    hours = total_min // 60
    minutes = total_min % 60
    start_time_str = f"{hours:02d}:{minutes:02d}"
    
    # Calculate end time
    end_min = total_min + duration
    end_hours = end_min // 60
    end_minutes = end_min % 60
    end_time_str = f"{end_hours:02d}:{end_minutes:02d}"
    
    print("SOLUTION:")
    print(f"Day: {selected_day}")
    print(f"Start Time: {start_time_str}")
    print(f"End Time: {end_time_str}")

solve_meeting_scheduling()