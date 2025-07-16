from z3 import *

def find_meeting_time():
    # Define the work hours
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60    # 17:00 in minutes
    meeting_duration = 60  # 1 hour in minutes

    # Define the participants' busy times in minutes since midnight
    # Each entry is (start, end)
    stephanie_busy = [(10 * 60, 10 * 60 + 30), (16 * 60, 16 * 60 + 30)]
    cheryl_busy = [(10 * 60, 10 * 60 + 30), (11 * 60 + 30, 12 * 60),
                   (13 * 60 + 30, 14 * 60), (16 * 60 + 30, 17 * 60)]
    bradley_busy = [(9 * 60 + 30, 10 * 60), (10 * 60 + 30, 11 * 60 + 30),
                    (13 * 60 + 30, 14 * 60), (14 * 60 + 30, 15 * 60),
                    (15 * 60 + 30, 17 * 60)]
    steven_busy = [(9 * 60, 12 * 60), (13 * 60, 13 * 60 + 30),
                   (14 * 60 + 30, 17 * 60)]

    # Create a Z3 solver instance
    solver = Solver()

    # Define the start time variable (in minutes since midnight)
    start_time = Int('start_time')

    # Constraint: start time must be within work hours
    solver.add(start_time >= work_start)
    solver.add(start_time + meeting_duration <= work_end)

    # Function to add constraints that the meeting does not overlap with busy times
    def add_no_overlap_constraints(busy_times):
        for (busy_start, busy_end) in busy_times:
            solver.add(Or(
                start_time + meeting_duration <= busy_start,
                start_time >= busy_end
            ))

    # Add no-overlap constraints for each participant
    add_no_overlap_constraints(stephanie_busy)
    add_no_overlap_constraints(cheryl_busy)
    add_no_overlap_constraints(bradley_busy)
    add_no_overlap_constraints(steven_busy)

    # Check if there's a solution
    if solver.check() == sat:
        model = solver.model()
        start_minutes = model[start_time].as_long()

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
        print("No solution found.")

find_meeting_time()