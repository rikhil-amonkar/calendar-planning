from z3 import *

def solve_meeting_scheduling():
    # Create a solver instance
    solver = Solver()
    
    # Possible days: Monday (0) or Tuesday (1)
    day = Int('day')
    solver.add(Or(day == 0, day == 1))
    
    # Start time in minutes from 9:00 (540 minutes)
    start_time = Int('start_time')
    # Meeting duration is 60 minutes
    duration = 60
    # Work hours: 9:00 (540) to 17:00 (1020)
    solver.add(start_time >= 540)
    solver.add(start_time + duration <= 1020)
    
    # Russell's busy times:
    # Monday: 10:30-11:00 (630-660)
    # Tuesday: 13:00-13:30 (780-810)
    # Alexander's busy times:
    # Monday: 9:00-11:30 (540-690), 12:00-14:30 (720-870), 15:00-17:00 (900-1020)
    # Tuesday: 9:00-10:00 (540-600), 13:00-14:00 (780-840), 15:00-15:30 (900-930), 16:00-16:30 (960-990)
    
    # Russell's preference: not Tuesday before 13:30 (i.e., if day is Tuesday, start_time >= 810)
    solver.add(Implies(day == 1, start_time >= 810))
    
    # Constraints for Russell's availability
    # On Monday, not overlapping with 10:30-11:00 (630-660)
    russell_monday_constraint = Or(
        day != 0,
        And(start_time + duration <= 630, start_time >= 540),
        And(start_time >= 660, start_time + duration <= 1020)
    )
    # On Tuesday, not overlapping with 13:00-13:30 (780-810)
    russell_tuesday_constraint = Or(
        day != 1,
        And(start_time + duration <= 780, start_time >= 810),
        And(start_time >= 810, start_time + duration <= 1020)
    )
    solver.add(russell_monday_constraint)
    solver.add(russell_tuesday_constraint)
    
    # Constraints for Alexander's availability
    # On Monday, not overlapping with 9:00-11:30 (540-690), 12:00-14:30 (720-870), 15:00-17:00 (900-1020)
    alexander_monday_constraint = Or(
        day != 0,
        And(start_time >= 690, start_time + duration <= 720),
        And(start_time >= 870, start_time + duration <= 900)
    )
    # On Tuesday, not overlapping with 9:00-10:00 (540-600), 13:00-14:00 (780-840), 15:00-15:30 (900-930), 16:00-16:30 (960-990)
    alexander_tuesday_constraint = Or(
        day != 1,
        And(start_time >= 600, start_time + duration <= 780),
        And(start_time >= 840, start_time + duration <= 900),
        And(start_time >= 930, start_time + duration <= 960),
        And(start_time >= 990, start_time + duration <= 1020)
    )
    solver.add(alexander_monday_constraint)
    solver.add(alexander_tuesday_constraint)
    
    # Check if there's a solution
    if solver.check() == sat:
        model = solver.model()
        day_val = model[day].as_long()
        start_time_val = model[start_time].as_long()
        
        # Convert start_time_val (minutes from midnight) to HH:MM
        hours = start_time_val // 60
        minutes = start_time_val % 60
        start_time_str = f"{hours:02d}:{minutes:02d}"
        
        end_time_val = start_time_val + duration
        end_hours = end_time_val // 60
        end_minutes = end_time_val % 60
        end_time_str = f"{end_hours:02d}:{end_minutes:02d}"
        
        day_str = "Monday" if day_val == 0 else "Tuesday"
        
        print("SOLUTION:")
        print(f"Day: {day_str}")
        print(f"Start Time: {start_time_str}")
        print(f"End Time: {end_time_str}")
    else:
        print("No solution found")

solve_meeting_scheduling()