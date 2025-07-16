from z3 import *

def solve_scheduling():
    # Initialize the solver
    solver = Solver()
    
    # Define the possible start times (in minutes from 9:00)
    start_time = Int('start_time')
    
    # Meeting duration is 30 minutes
    duration = 30
    
    # Work hours are from 9:00 (540 minutes) to 17:00 (1020 minutes)
    min_time = 540  # 9:00 in minutes
    max_time = 1020 - duration  # 17:00 - 30 minutes
    
    # Constraint: start time must be within work hours
    solver.add(start_time >= min_time, start_time <= max_time)
    
    # Each participant's busy intervals in minutes from 9:00
    # Kimberly's busy intervals: 10:00-10:30, 11:00-12:00, 16:00-16:30
    kimberly_busy = [(600, 630), (660, 720), (960, 990)]
    # Marie's busy intervals: 10:00-11:00, 11:30-15:00, 16:00-16:30
    marie_busy = [(600, 660), (690, 900), (960, 990)]
    # Diana's busy intervals: 9:30-10:00, 10:30-14:30, 15:30-17:00
    diana_busy = [(570, 600), (630, 870), (930, 1020)]
    # Megan has no meetings but prefers not before 10:00
    megan_preference_start = 600  # 10:00
    
    # Add constraints for each participant
    # Kimberly: meeting should not overlap with her busy times
    for (s, e) in kimberly_busy:
        solver.add(Or(start_time >= e, start_time + duration <= s))
    
    # Marie: meeting should not overlap with her busy times
    for (s, e) in marie_busy:
        solver.add(Or(start_time >= e, start_time + duration <= s))
    
    # Diana: meeting should not overlap with her busy times
    for (s, e) in diana_busy:
        solver.add(Or(start_time >= e, start_time + duration <= s))
    
    # Megan: no meetings before 10:00
    solver.add(start_time >= megan_preference_start)
    
    # Check for a solution
    if solver.check() == sat:
        model = solver.model()
        start_minutes = model[start_time].as_long()
        
        # Convert minutes back to HH:MM format
        start_hh = start_minutes // 60
        start_mm = start_minutes % 60
        end_minutes = start_minutes + duration
        end_hh = end_minutes // 60
        end_mm = end_minutes % 60
        
        # Format the output
        print("SOLUTION:")
        print("Day: Monday")
        print(f"Start Time: {start_hh:02d}:{start_mm:02d}")
        print(f"End Time: {end_hh:02d}:{end_mm:02d}")
    else:
        print("No solution found")

solve_scheduling()