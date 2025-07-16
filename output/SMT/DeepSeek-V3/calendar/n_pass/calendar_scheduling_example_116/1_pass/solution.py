from z3 import *

def solve_scheduling():
    # Define the start time in minutes from 9:00 (540 minutes from midnight)
    start_time = Int('start_time')
    
    # Work hours: 9:00 to 17:00 (540 to 1020 minutes)
    work_start = 540
    work_end = 1020
    meeting_duration = 30
    
    # Create solver instance
    solver = Solver()
    
    # Constraint: meeting must be within work hours
    solver.add(start_time >= work_start)
    solver.add(start_time + meeting_duration <= work_end)
    
    # Participants' busy times in minutes from 9:00 (subtract 540 to get minutes from 9:00)
    # Adam: 14:00-15:00 → 840-900
    # John: 13:00-13:30 → 780-810, 14:00-14:30 → 840-870, 15:30-16:00 → 930-960, 16:30-17:00 → 990-1020
    # Stephanie: 9:30-10:00 → 570-600, 10:30-11:00 → 630-660, 11:30-16:00 → 690-960, 16:30-17:00 → 990-1020
    # Anna: 9:30-10:00 → 570-600, 12:00-12:30 → 720-750, 13:00-15:30 → 780-930, 16:30-17:00 → 990-1020
    
    # Anna's preference: not before 14:30 → start_time >= 870 (14:30 is 870 minutes from midnight)
    solver.add(start_time >= 870)
    
    # Adam's busy: 840-900
    solver.add(Or(
        start_time + meeting_duration <= 840,
        start_time >= 900
    ))
    
    # John's busy: 780-810, 840-870, 930-960, 990-1020
    solver.add(Or(
        start_time + meeting_duration <= 780,
        And(start_time >= 810, start_time + meeting_duration <= 840),
        And(start_time >= 870, start_time + meeting_duration <= 930),
        And(start_time >= 960, start_time + meeting_duration <= 990)
    ))
    
    # Stephanie's busy: 570-600, 630-660, 690-960, 990-1020
    solver.add(Or(
        start_time + meeting_duration <= 570,
        And(start_time >= 600, start_time + meeting_duration <= 630),
        And(start_time >= 660, start_time + meeting_duration <= 690),
        start_time >= 960
    ))
    
    # Anna's busy: 570-600, 720-750, 780-930, 990-1020
    solver.add(Or(
        start_time + meeting_duration <= 570,
        And(start_time >= 600, start_time + meeting_duration <= 720),
        And(start_time >= 750, start_time + meeting_duration <= 780),
        start_time >= 930
    ))
    
    # Check for a solution
    if solver.check() == sat:
        model = solver.model()
        start_min = model[start_time].as_long()
        
        # Convert minutes back to HH:MM
        start_hour = start_min // 60
        start_min = start_min % 60
        end_min_total = start_min + meeting_duration
        end_hour = start_hour + (end_min_total // 60)
        end_min = end_min_total % 60
        
        # Format the output
        print("SOLUTION:")
        print("Day: Monday")
        print(f"Start Time: {start_hour:02d}:{start_min:02d}")
        print(f"End Time: {end_hour:02d}:{end_min:02d}")
    else:
        print("No solution found")

solve_scheduling()