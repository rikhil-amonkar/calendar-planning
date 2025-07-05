from z3 import *

def solve_scheduling():
    # Define the work hours
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60    # 17:00 in minutes
    meeting_duration = 30  # minutes

    # Define the participants' blocked times in minutes since midnight
    bradley_blocked = [
        (9 * 60 + 30, 10 * 60),      # 9:30-10:00
        (12 * 60 + 30, 13 * 60),     # 12:30-13:00
        (13 * 60 + 30, 14 * 60),     # 13:30-14:00
        (15 * 60 + 30, 16 * 60)      # 15:30-16:00
    ]
    teresa_blocked = [
        (10 * 60 + 30, 11 * 60),     # 10:30-11:00
        (12 * 60, 12 * 60 + 30),     # 12:00-12:30
        (13 * 60, 13 * 60 + 30),     # 13:00-13:30
        (14 * 60 + 30, 15 * 60)      # 14:30-15:00
    ]
    elizabeth_blocked = [
        (9 * 60, 9 * 60 + 30),       # 9:00-9:30
        (10 * 60 + 30, 11 * 60 + 30), # 10:30-11:30
        (13 * 60, 13 * 60 + 30),     # 13:00-13:30
        (14 * 60 + 30, 15 * 60),     # 14:30-15:00
        (15 * 60 + 30, 17 * 60)      # 15:30-17:00
    ]
    christian_blocked = [
        (9 * 60, 9 * 60 + 30),       # 9:00-9:30
        (10 * 60 + 30, 17 * 60)      # 10:30-17:00
    ]

    # Create a Z3 solver instance
    solver = Solver()

    # Define the start time variable (in minutes since midnight)
    start_time = Int('start_time')

    # Add constraints for the start time
    solver.add(start_time >= work_start)
    solver.add(start_time + meeting_duration <= work_end)

    # Function to check if a time range overlaps with any blocked time
    def no_overlap(start, end, blocked_times):
        return And([Or(end <= block_start, start >= block_end) for (block_start, block_end) in blocked_times])

    # Add constraints for each participant's availability
    solver.add(no_overlap(start_time, start_time + meeting_duration, bradley_blocked))
    solver.add(no_overlap(start_time, start_time + meeting_duration, teresa_blocked))
    solver.add(no_overlap(start_time, start_time + meeting_duration, elizabeth_blocked))
    solver.add(no_overlap(start_time, start_time + meeting_duration, christian_blocked))

    # Check if there's a solution
    if solver.check() == sat:
        model = solver.model()
        start_minutes = model.evaluate(start_time).as_long()
        
        # Convert minutes back to HH:MM format
        start_hh = start_minutes // 60
        start_mm = start_minutes % 60
        end_minutes = start_minutes + meeting_duration
        end_hh = end_minutes // 60
        end_mm = end_minutes % 60
        
        # Format the output
        print("SOLUTION:")
        print(f"Day: Monday")
        print(f"Start Time: {start_hh:02d}:{start_mm:02d}")
        print(f"End Time: {end_hh:02d}:{end_mm:02d}")
    else:
        print("No solution found")

solve_scheduling()