from z3 import *

def solve_scheduling():
    # Initialize the solver
    s = Solver()
    
    # Work hours are 9:00 to 17:00 (9*60 to 17*60 in minutes)
    work_start = 9 * 60
    work_end = 17 * 60
    
    # Meeting duration is 30 minutes
    duration = 30
    
    # Define the start time variable (in minutes from 0:00)
    start_time = Int('start_time')
    
    # Constraints for the meeting to be within work hours
    s.add(start_time >= work_start)
    s.add(start_time + duration <= work_end)
    
    # Megan's preference: avoid before 10:00
    s.add(Not(And(start_time >= work_start, start_time < 10 * 60)))
    
    # Define each person's busy intervals in minutes from 0:00
    kimberly_busy = [(10*60, 10*60 + 30), (11*60, 12*60), (16*60, 16*60 + 30)]
    marie_busy = [(10*60, 11*60), (11*60 + 30, 15*60), (16*60, 16*60 + 30)]
    diana_busy = [(9*60 + 30, 10*60), (10*60 + 30, 14*60 + 30), (15*60 + 30, 17*60)]
    # Megan has no meetings
    
    # Function to add no-overlap constraints for a person's busy intervals
    def add_no_overlap_constraints(busy_intervals):
        for (busy_start, busy_end) in busy_intervals:
            s.add(Not(And(start_time < busy_end, start_time + duration > busy_start)))
    
    # Add constraints for each person
    add_no_overlap_constraints(kimberly_busy)
    add_no_overlap_constraints(marie_busy)
    add_no_overlap_constraints(diana_busy)
    
    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        start_min = m.evaluate(start_time).as_long()
        
        # Convert start time to HH:MM format
        start_hh = start_min // 60
        start_mm = start_min % 60
        start_time_str = f"{start_hh:02d}:{start_mm:02d}"
        
        # Calculate end time
        end_min = start_min + duration
        end_hh = end_min // 60
        end_mm = end_min % 60
        end_time_str = f"{end_hh:02d}:{end_mm:02d}"
        
        # Output the solution
        print("SOLUTION:")
        print(f"Day: Monday")
        print(f"Start Time: {start_time_str}")
        print(f"End Time: {end_time_str}")
    else:
        print("No solution found")

solve_scheduling()