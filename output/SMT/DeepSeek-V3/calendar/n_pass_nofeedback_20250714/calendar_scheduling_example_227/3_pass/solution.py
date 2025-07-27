from z3 import *

def solve_scheduling():
    # Initialize Z3 solver
    solver = Solver()
    
    # Define the start time in minutes from 9:00 (0 to 480, since 17:00 is 8 hours after 9:00)
    start_time = Int('start_time')
    meeting_duration = 30  # minutes
    
    # Constraints: start_time must be within 9:00 to 16:30 (since meeting is 30 minutes)
    solver.add(start_time >= 0)
    solver.add(start_time <= 480 - meeting_duration)
    
    # Convert all busy times to minutes from 9:00
    # Each busy time is a tuple (start, end)
    
    # David's busy times: 11:30-12:00, 14:30-15:00
    david_busy = [(150, 180), (270, 300)]
    # Douglas's busy times: 9:30-10:00, 11:30-12:00, 13:00-13:30, 14:30-15:00
    douglas_busy = [(30, 60), (150, 180), (120, 150), (270, 300)]
    # Ralph's busy times: 9:00-9:30, 10:00-11:00, 11:30-12:30, 13:30-15:00, 15:30-16:00, 16:30-17:00
    ralph_busy = [(0, 30), (60, 120), (150, 210), (210, 300), (330, 360), (390, 480)]
    # Jordan's busy times: 9:00-10:00, 12:00-12:30, 13:00-13:30, 14:30-15:00, 15:30-17:00
    jordan_busy = [(0, 60), (180, 210), (120, 150), (270, 300), (330, 480)]
    
    # David's preference: not before 14:00 (14:00 is 300 minutes from 9:00)
    solver.add(start_time >= 300)
    
    # Function to add no-overlap constraints
    def add_no_overlap(busy_times):
        for (busy_start, busy_end) in busy_times:
            solver.add(Or(
                start_time + meeting_duration <= busy_start,
                start_time >= busy_end
            ))
    
    # Natalie is free all day, no constraints
    # Add constraints for others
    add_no_overlap(david_busy)
    add_no_overlap(douglas_busy)
    add_no_overlap(ralph_busy)
    add_no_overlap(jordan_busy)
    
    # Check for solution
    if solver.check() == sat:
        model = solver.model()
        start_minutes = model.evaluate(start_time).as_long()
        
        # Convert minutes back to HH:MM
        hours = 9 + start_minutes // 60
        minutes = start_minutes % 60
        start_time_str = f"{hours:02d}:{minutes:02d}"
        
        end_minutes = start_minutes + meeting_duration
        end_hours = 9 + end_minutes // 60
        end_minutes_remainder = end_minutes % 60
        end_time_str = f"{end_hours:02d}:{end_minutes_remainder:02d}"
        
        print("SOLUTION:")
        print(f"Day: Monday")
        print(f"Start Time: {start_time_str}")
        print(f"End Time: {end_time_str}")
    else:
        print("No solution found")

solve_scheduling()