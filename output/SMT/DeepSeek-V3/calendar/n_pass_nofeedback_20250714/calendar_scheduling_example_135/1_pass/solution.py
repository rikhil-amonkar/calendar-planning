from z3 import *

def solve_scheduling():
    # Initialize the solver
    solver = Solver()
    
    # The meeting duration is 30 minutes
    duration = 30
    
    # Work hours are from 9:00 to 17:00 (9 AM to 5 PM)
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60    # 17:00 in minutes
    
    # Define the start time variable (in minutes since midnight)
    start_time = Int('start_time')
    
    # Constraint: start time must be within work hours and leave room for the duration
    solver.add(start_time >= work_start)
    solver.add(start_time + duration <= work_end)
    
    # Define each participant's busy intervals in minutes since midnight
    # Eric has no meetings, so no constraints
    
    # Ashley's busy intervals:
    ashley_busy = [
        (10 * 60, 10 * 60 + 30),    # 10:00-10:30
        (11 * 60, 12 * 60),         # 11:00-12:00
        (12 * 60 + 30, 13 * 60),    # 12:30-13:00
        (15 * 60, 16 * 60)          # 15:00-16:00
    ]
    
    # Ronald's busy intervals:
    ronald_busy = [
        (9 * 60, 9 * 60 + 30),      # 9:00-9:30
        (10 * 60, 11 * 60 + 30),    # 10:00-11:30
        (12 * 60 + 30, 14 * 60),    # 12:30-14:00
        (14 * 60 + 30, 17 * 60)     # 14:30-17:00
    ]
    
    # Larry's busy intervals:
    larry_busy = [
        (9 * 60, 12 * 60),          # 9:00-12:00
        (13 * 60, 17 * 60)          # 13:00-17:00
    ]
    
    # Function to add no-overlap constraints for a list of busy intervals
    def add_no_overlap_constraints(busy_intervals):
        for (busy_start, busy_end) in busy_intervals:
            # The meeting must not overlap with this busy interval
            solver.add(Or(
                start_time + duration <= busy_start,
                start_time >= busy_end
            ))
    
    # Add constraints for each participant
    add_no_overlap_constraints(ashley_busy)
    add_no_overlap_constraints(ronald_busy)
    add_no_overlap_constraints(larry_busy)
    
    # Check if a solution exists
    if solver.check() == sat:
        model = solver.model()
        start_minutes = model.evaluate(start_time).as_long()
        
        # Convert minutes back to HH:MM format
        hours = start_minutes // 60
        minutes = start_minutes % 60
        start_time_str = f"{hours:02d}:{minutes:02d}"
        
        end_minutes = start_minutes + duration
        end_hours = end_minutes // 60
        end_minutes = end_minutes % 60
        end_time_str = f"{end_hours:02d}:{end_minutes:02d}"
        
        # Print the solution in the required format
        print("SOLUTION:")
        print("Day: Monday")
        print(f"Start Time: {start_time_str}")
        print(f"End Time: {end_time_str}")
    else:
        print("No solution found")

solve_scheduling()