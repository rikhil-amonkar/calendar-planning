from z3 import *

def solve_meeting_scheduling():
    # Initialize the solver
    solver = Solver()
    
    # Work hours are 9:00 to 17:00 (9*60 to 17*60 in minutes)
    work_start = 9 * 60
    work_end = 17 * 60
    
    # Meeting duration is 30 minutes
    duration = 30
    
    # Define the start time variable (in minutes from 0:00)
    start_time = Int('start_time')
    
    # Constraints for work hours
    solver.add(start_time >= work_start)
    solver.add(start_time + duration <= work_end)
    
    # Billy's preference: meeting should end by 15:00 (so start by 14:30)
    solver.add(start_time + duration <= 15 * 60)
    
    # Participants' blocked times in minutes since midnight
    # Raymond's blocked times
    raymond_blocked = [
        (9 * 60, 9 * 60 + 30),    # 9:00-9:30
        (11 * 60 + 30, 12 * 60),  # 11:30-12:00
        (13 * 60, 13 * 60 + 30),   # 13:00-13:30
        (15 * 60, 15 * 60 + 30)    # 15:00-15:30
    ]
    
    # Billy's blocked times
    billy_blocked = [
        (10 * 60, 10 * 60 + 30),   # 10:00-10:30
        (12 * 60, 13 * 60),         # 12:00-13:00
        (16 * 60 + 30, 17 * 60)     # 16:30-17:00
    ]
    
    # Donald's blocked times
    donald_blocked = [
        (9 * 60, 9 * 60 + 30),      # 9:00-9:30
        (10 * 60, 11 * 60),          # 10:00-11:00
        (12 * 60, 13 * 60),         # 12:00-13:00
        (14 * 60, 14 * 60 + 30),     # 14:00-14:30
        (16 * 60, 17 * 60)           # 16:00-17:00
    ]
    
    # Function to add no-overlap constraints for a participant's blocked times
    def add_no_overlap_constraints(blocked_times):
        for (block_start, block_end) in blocked_times:
            solver.add(Or(
                start_time + duration <= block_start,
                start_time >= block_end
            ))
    
    # Add constraints for each participant
    add_no_overlap_constraints(raymond_blocked)
    add_no_overlap_constraints(billy_blocked)
    add_no_overlap_constraints(donald_blocked)
    
    # Check for a solution
    if solver.check() == sat:
        model = solver.model()
        start_minutes = model.evaluate(start_time).as_long()
        
        # Convert minutes back to HH:MM format
        hours = start_minutes // 60
        minutes = start_minutes % 60
        start_time_str = f"{hours:02d}:{minutes:02d}"
        
        end_minutes = start_minutes + duration
        end_hours = end_minutes // 60
        end_minutes_remainder = end_minutes % 60
        end_time_str = f"{end_hours:02d}:{end_minutes_remainder:02d}"
        
        print("SOLUTION:")
        print("Day: Monday")
        print(f"Start Time: {start_time_str}")
        print(f"End Time: {end_time_str}")
    else:
        print("No solution found")

# Call the function to solve the problem
solve_meeting_scheduling()