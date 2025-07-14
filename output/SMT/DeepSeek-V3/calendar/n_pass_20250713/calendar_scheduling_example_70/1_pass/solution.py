from z3 import *

def solve_scheduling():
    # Define the work hours in minutes from midnight
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    meeting_duration = 30  # minutes

    # Create a solver instance
    solver = Optimize()

    # Define the start time variable (in minutes since midnight)
    start_time = Int('start_time')

    # Constraints for work hours: meeting must start and end within work hours
    solver.add(start_time >= work_start)
    solver.add(start_time + meeting_duration <= work_end)

    # Define each participant's busy times in minutes since midnight
    # Denise's busy times: 12:00-12:30 (720-750), 15:30-16:00 (930-960)
    denise_busy = [(12 * 60, 12 * 60 + 30), (15 * 60 + 30, 16 * 60)]
    # Natalie's busy times: 9:00-11:30 (540-690), 12:00-13:00 (720-780), 14:00-14:30 (840-870), 15:00-17:00 (900-1020)
    natalie_busy = [(9 * 60, 11 * 60 + 30), (12 * 60, 13 * 60), (14 * 60, 14 * 60 + 30), (15 * 60, 17 * 60)]
    # Angela has no meetings, so no constraints

    # Function to add constraints that the meeting does not overlap with any busy intervals
    def add_no_overlap_constraints(busy_intervals):
        for (busy_start, busy_end) in busy_intervals:
            # The meeting must be either entirely before or entirely after the busy interval
            solver.add(Or(
                start_time + meeting_duration <= busy_start,
                start_time >= busy_end
            ))

    # Add constraints for Denise and Natalie
    add_no_overlap_constraints(denise_busy)
    add_no_overlap_constraints(natalie_busy)

    # Objective: minimize the start time to find the earliest possible meeting
    solver.minimize(start_time)

    # Check if a solution exists
    if solver.check() == sat:
        model = solver.model()
        start_minutes = model.eval(start_time).as_long()

        # Convert minutes back to HH:MM format
        hours = start_minutes // 60
        minutes = start_minutes % 60
        start_time_str = f"{hours:02d}:{minutes:02d}"

        end_minutes = start_minutes + meeting_duration
        end_hours = end_minutes // 60
        end_minutes_remainder = end_minutes % 60
        end_time_str = f"{end_hours:02d}:{end_minutes_remainder:02d}"

        # Output the solution
        print("SOLUTION:")
        print(f"Day: Monday")
        print(f"Start Time: {start_time_str}")
        print(f"End Time: {end_time_str}")
    else:
        print("No solution found")

solve_scheduling()