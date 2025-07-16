from z3 import *

def solve_scheduling():
    # Initialize the solver
    s = Solver()
    
    # Work hours are 9:00 to 17:00 (9*60 = 540 to 17*60 = 1020 minutes in 24-hour format)
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    meeting_duration = 30
    
    # The start time of the meeting in minutes from 0:00 (but constrained within work hours)
    start_time = Int('start_time')
    
    # Constraints for the meeting to be within work hours and duration
    s.add(start_time >= work_start)
    s.add(start_time + meeting_duration <= work_end)
    
    # Each participant's blocked times in minutes (start and end)
    # Blocked times are represented as pairs (start, end) in minutes since midnight
    joe_blocked = [(9*60 + 30, 10*60), (10*60 + 30, 11*60)]
    keith_blocked = [(11*60 + 30, 12*60), (15*60, 15*60 + 30)]
    patricia_blocked = [(9*60, 9*60 + 30), (13*60, 13*60 + 30)]
    nancy_blocked = [(9*60, 11*60), (11*60 + 30, 16*60 + 30)]
    pamela_blocked = [
        (9*60, 10*60),
        (10*60 + 30, 11*60),
        (11*60 + 30, 12*60 + 30),
        (13*60, 14*60),
        (14*60 + 30, 15*60),
        (15*60 + 30, 16*60),
        (16*60 + 30, 17*60)
    ]
    
    all_blocked = joe_blocked + keith_blocked + patricia_blocked + nancy_blocked + pamela_blocked
    
    # Function to add no-overlap constraints for a list of blocked intervals
    def add_no_overlap_constraints(blocked_intervals):
        for (block_start, block_end) in blocked_intervals:
            # The meeting does not overlap with this blocked interval if:
            # meeting ends before block_start OR meeting starts after block_end
            s.add(Or(
                start_time + meeting_duration <= block_start,
                start_time >= block_end
            ))
    
    add_no_overlap_constraints(joe_blocked)
    add_no_overlap_constraints(keith_blocked)
    add_no_overlap_constraints(patricia_blocked)
    add_no_overlap_constraints(nancy_blocked)
    add_no_overlap_constraints(pamela_blocked)
    
    # Check if there's a solution
    if s.check() == sat:
        m = s.model()
        start_minutes = m.evaluate(start_time).as_long()
        
        # Convert minutes back to HH:MM format
        start_hh = start_minutes // 60
        start_mm = start_minutes % 60
        end_minutes = start_minutes + meeting_duration
        end_hh = end_minutes // 60
        end_mm = end_minutes % 60
        
        print("SOLUTION:")
        print(f"Day: Monday")
        print(f"Start Time: {start_hh:02d}:{start_mm:02d}")
        print(f"End Time: {end_hh:02d}:{end_mm:02d}")
    else:
        print("No solution found")

solve_scheduling()