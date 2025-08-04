from z3 import *

def solve_scheduling_problem():
    # Initialize the solver
    solver = Optimize()
    
    # Define variables
    day = Int('day')  # 0: Monday, 1: Tuesday, 2: Wednesday
    start_time = Int('start_time')  # in minutes from 9:00 (e.g., 0 is 9:00, 30 is 9:30)
    end_time = Int('end_time')
    
    # Meeting duration is 30 minutes
    solver.add(end_time == start_time + 30)
    
    # Meeting must be within work hours (9:00 to 17:00, so 0 to 480 minutes from 9:00)
    solver.add(start_time >= 0)
    solver.add(end_time <= 480)  # 480 minutes = 8 hours after 9:00 is 17:00
    
    # Day must be 0 (Monday), 1 (Tuesday), or 2 (Wednesday)
    solver.add(day >= 0, day <= 2)
    
    # Larry's calendar is wide open, so no constraints from him except preferences
    # Samuel's existing meetings:
    # Monday: 10:30-11:00 (90-120), 12:00-12:30 (180-210), 13:00-15:00 (240-360), 15:30-16:30 (390-450)
    # Tuesday: 9:00-12:00 (0-180), 14:00-15:30 (300-390), 16:30-17:00 (450-480)
    # Wednesday: 10:30-11:00 (90-120), 11:30-12:00 (150-180), 12:30-13:00 (210-240), 14:00-14:30 (300-330), 15:00-16:00 (360-420)
    
    # Constraints for Samuel's existing meetings based on the day
    # For each day, the meeting must not overlap with Samuel's existing meetings
    # Monday
    monday_constraints = Or(
        And(day != 0),  # if not Monday, no constraints
        And(day == 0,
            Or(
                end_time <= 90,   # before 10:30
                And(start_time >= 120, end_time <= 180),  # between 11:00 and 12:00
                And(start_time >= 210, end_time <= 240),  # between 12:30 and 13:00
                And(start_time >= 360, end_time <= 390),  # between 15:00 and 15:30
                start_time >= 450  # after 16:30
            )
        )
    )
    
    # Tuesday
    tuesday_constraints = Or(
        And(day != 1),
        And(day == 1,
            Or(
                end_time <= 0,   # impossible, so effectively no available time unless between other meetings
                And(start_time >= 180, end_time <= 300),  # between 12:00 and 14:00
                And(start_time >= 390, end_time <= 450),  # between 15:30 and 16:30
                start_time >= 480  # impossible
            )
        )
    )
    # But Samuel wants to avoid more meetings on Tuesday, so we'll add a soft constraint to avoid day 1
    # However, if no other options, it's allowed
    
    # Wednesday
    wednesday_constraints = Or(
        And(day != 2),
        And(day == 2,
            Or(
                end_time <= 90,   # before 10:30
                And(start_time >= 120, end_time <= 150),  # between 11:00 and 11:30
                And(start_time >= 180, end_time <= 210),  # between 12:00 and 12:30
                And(start_time >= 240, end_time <= 300),  # between 13:00 and 14:00
                And(start_time >= 330, end_time <= 360),  # between 14:30 and 15:00
                start_time >= 420  # after 16:00
            )
        )
    )
    
    solver.add(monday_constraints)
    solver.add(tuesday_constraints)
    solver.add(wednesday_constraints)
    
    # Preferences: Larry would rather not meet on Wednesday (day 2), Samuel avoid Tuesday (day 1)
    # We'll add soft constraints to minimize day and start time
    # To prioritize earlier days and times, we'll minimize (day * 1000 + start_time)
    objective = day * 1000 + start_time
    solver.minimize(objective)
    
    # Check if the problem is satisfiable
    if solver.check() == sat:
        model = solver.model()
        day_val = model[day].as_long()
        start_val = model[start_time].as_long()
        end_val = model[end_time].as_long()
        
        # Convert day_val to day name
        days = ['Monday', 'Tuesday', 'Wednesday']
        day_name = days[day_val]
        
        # Convert start and end times to HH:MM format
        start_hh = 9 + start_val // 60
        start_mm = start_val % 60
        end_hh = 9 + end_val // 60
        end_mm = end_val % 60
        
        # Format as strings with leading zeros
        start_time_str = f"{start_hh:02d}:{start_mm:02d}"
        end_time_str = f"{end_hh:02d}:{end_mm:02d}"
        
        # Print the solution
        print("SOLUTION:")
        print(f"Day: {day_name}")
        print(f"Start Time: {start_time_str}")
        print(f"End Time: {end_time_str}")
    else:
        print("No solution found")

solve_scheduling_problem()