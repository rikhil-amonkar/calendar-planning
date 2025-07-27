from z3 import *

def solve_scheduling():
    # Define the work hours and meeting duration
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60    # 17:00 in minutes
    meeting_duration = 30  # minutes

    # Define the blocked times for Eric and Henry in minutes since 9:00
    # Eric's blocked times: 12:00-13:00, 14:00-15:00
    eric_blocked = [(12*60, 13*60), (14*60, 15*60)]
    # Henry's blocked times: 9:30-10:00, 10:30-11:00, 11:30-12:30, 13:00-13:30, 14:30-15:00, 16:00-17:00
    henry_blocked = [(9*60 + 30, 10*60), (10*60 + 30, 11*60), (11*60 + 30, 12*60 + 30),
                     (13*60, 13*60 + 30), (14*60 + 30, 15*60), (16*60, 17*60)]

    # Create a Z3 solver instance
    s = Solver()

    # Define the start time of the meeting as an integer variable
    start_time = Int('start_time')
    s.add(start_time >= work_start)
    s.add(start_time + meeting_duration <= work_end)

    # Add constraints for Eric's availability
    for (block_start, block_end) in eric_blocked:
        s.add(Or(start_time + meeting_duration <= block_start, start_time >= block_end))

    # Add constraints for Henry's availability
    for (block_start, block_end) in henry_blocked:
        s.add(Or(start_time + meeting_duration <= block_start, start_time >= block_end))

    # Henry's preference: try to schedule before 10:00 if possible
    preferred_start = Int('preferred_start')
    s.add(preferred_start == start_time)
    s.add_soft(preferred_start + meeting_duration <= 10 * 60)

    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        start = m[start_time].as_long()
        # Convert minutes back to HH:MM format
        start_hh = start // 60
        start_mm = start % 60
        end = start + meeting_duration
        end_hh = end // 60
        end_mm = end % 60
        # Format the output
        print("SOLUTION:")
        print(f"Day: Monday")
        print(f"Start Time: {start_hh:02d}:{start_mm:02d}")
        print(f"End Time: {end_hh:02d}:{end_mm:02d}")
    else:
        print("No solution found")

solve_scheduling()