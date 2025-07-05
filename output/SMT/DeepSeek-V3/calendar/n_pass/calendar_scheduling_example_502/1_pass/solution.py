from z3 import *

def solve_scheduling():
    # Initialize the solver
    s = Solver()
    
    # Define the start time as an integer (minutes from 9:00)
    start_time = Int('start_time')
    
    # Work hours are 9:00 to 17:00 (480 minutes from 9:00 to 17:00)
    # Meeting duration is 30 minutes
    duration = 30
    min_time = 9 * 60  # 9:00 in minutes
    max_time = 17 * 60 - duration  # 17:00 - 30 minutes
    
    # Constraint: start_time must be within work hours and allow 30-minute meeting
    s.add(start_time >= min_time)
    s.add(start_time <= max_time)
    
    # Jack's busy intervals in minutes from 9:00
    jack_busy = [
        (9*60 + 30, 10*60 + 30),   # 9:30-10:30
        (11*60 + 0, 11*60 + 30),    # 11:00-11:30
        (12*60 + 30, 13*60 + 0),    # 12:30-13:00
        (14*60 + 0, 14*60 + 30),    # 14:00-14:30
        (16*60 + 0, 16*60 + 30)     # 16:00-16:30
    ]
    
    # Charlotte's busy intervals
    charlotte_busy = [
        (9*60 + 30, 10*60 + 0),    # 9:30-10:00
        (10*60 + 30, 12*60 + 0),    # 10:30-12:00
        (12*60 + 30, 13*60 + 30),   # 12:30-13:30
        (14*60 + 0, 16*60 + 0)      # 14:00-16:00
    ]
    
    # Function to add no-overlap constraints for a list of busy intervals
    def add_no_overlap_constraints(busy_intervals):
        for (busy_start, busy_end) in busy_intervals:
            # The meeting does not overlap with this busy interval
            s.add(Or(
                start_time + duration <= busy_start,
                start_time >= busy_end
            ))
    
    # Add constraints for Jack and Charlotte's busy intervals
    add_no_overlap_constraints(jack_busy)
    add_no_overlap_constraints(charlotte_busy)
    
    # Jack's preference: avoid meetings after 12:30
    s.add(start_time <= 12*60 + 30 - duration)
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        solution_start = m.evaluate(start_time).as_long()
        
        # Convert minutes back to HH:MM format
        start_hh = solution_start // 60
        start_mm = solution_start % 60
        end_time = solution_start + duration
        end_hh = end_time // 60
        end_mm = end_time % 60
        
        # Format the output
        print("SOLUTION:")
        print(f"Day: Monday")
        print(f"Start Time: {start_hh:02d}:{start_mm:02d}")
        print(f"End Time: {end_hh:02d}:{end_mm:02d}")
    else:
        print("No solution found")

solve_scheduling()