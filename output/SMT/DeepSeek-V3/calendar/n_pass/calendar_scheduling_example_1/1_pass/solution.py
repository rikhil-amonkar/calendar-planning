from z3 import *

def solve_scheduling():
    # Initialize the solver
    solver = Solver()
    
    # Work hours are 9:00 to 17:00 (9*60 to 17*60 in minutes)
    work_start = 9 * 60
    work_end = 17 * 60
    meeting_duration = 30
    
    # Define the start time variable in minutes since 9:00 (0 is 9:00)
    start_time = Int('start_time')
    
    # Constraints for the start time to be within work hours and meeting fits
    solver.add(start_time >= 0)
    solver.add(start_time + meeting_duration <= work_end - work_start)
    
    # Convert each participant's busy slots to minutes since 9:00
    # Raymond's busy slots: 9:00-9:30 (0-30), 11:30-12:00 (150-180), 13:00-13:30 (240-270), 15:00-15:30 (360-390)
    raymond_busy = [
        (0, 30),
        (150, 180),
        (240, 270),
        (360, 390)
    ]
    
    # Billy's busy slots: 10:00-10:30 (60-90), 12:00-13:00 (180-240), 16:30-17:00 (450-480)
    billy_busy = [
        (60, 90),
        (180, 240),
        (450, 480)
    ]
    
    # Donald's busy slots: 9:00-9:30 (0-30), 10:00-11:00 (60-120), 12:00-13:00 (180-240), 14:00-14:30 (300-330), 16:00-17:00 (420-480)
    donald_busy = [
        (0, 30),
        (60, 120),
        (180, 240),
        (300, 330),
        (420, 480)
    ]
    
    # Function to add no-overlap constraints for a participant's busy slots
    def add_no_overlap(busy_slots):
        for (busy_start, busy_end) in busy_slots:
            solver.add(Or(
                start_time + meeting_duration <= busy_start,
                start_time >= busy_end
            ))
    
    # Add constraints for each participant
    add_no_overlap(raymond_busy)
    add_no_overlap(billy_busy)
    add_no_overlap(donald_busy)
    
    # Billy prefers no meetings after 15:00 (360 minutes since 9:00)
    # We'll first try to find a solution before 15:00, and if not, then after
    preferred_end = 360 - meeting_duration  # start_time must be <= 330 to end by 15:00
    
    # Try to find a solution before 15:00 first
    temp_solver = Solver()
    temp_solver.add(solver.assertions())
    temp_solver.add(start_time <= preferred_end)
    
    solution = None
    if temp_solver.check() == sat:
        model = temp_solver.model()
        solution = model[start_time].as_long()
    else:
        # If no solution before 15:00, try the original solver
        if solver.check() == sat:
            model = solver.model()
            solution = model[start_time].as_long()
    
    if solution is None:
        print("No solution found")
        return
    
    # Convert solution back to HH:MM format
    total_minutes = work_start + solution
    hours = total_minutes // 60
    minutes = total_minutes % 60
    start_time_str = f"{hours:02d}:{minutes:02d}"
    
    end_time = total_minutes + meeting_duration
    end_hours = end_time // 60
    end_minutes = end_time % 60
    end_time_str = f"{end_hours:02d}:{end_minutes:02d}"
    
    print("SOLUTION:")
    print(f"Day: Monday")
    print(f"Start Time: {start_time_str}")
    print(f"End Time: {end_time_str}")

solve_scheduling()