from z3 import *

def schedule_meeting(start_time, end_time, duration, christine_schedule, helen_schedule, helen_avoid_after):
    # Create Z3 variables for the meeting time
    christine_meeting = Int('christine_meeting')
    helen_meeting = Int('helen_meeting')

    # Create Z3 variables for the start and end times of the meeting
    meeting_start = Int('meeting_start')
    meeting_end = Int('meeting_end')

    # Define the constraints for the meeting time
    constraints = [
        And(christine_meeting >= start_time, christine_meeting <= end_time),
        And(helen_meeting >= start_time, helen_meeting <= end_time),
        meeting_start == christine_meeting,
        meeting_end == christine_meeting + duration,
        meeting_start == helen_meeting,
        meeting_end == helen_meeting + duration,
    ]

    # Define the constraints for Christine's schedule
    christine_constraints = []
    for start, end in christine_schedule:
        christine_constraints.extend([
            Not(And(christine_meeting >= start, christine_meeting < end)),
            Not(And(meeting_start >= start, meeting_start < end)),
            Not(And(meeting_end > start, meeting_end <= end)),
        ])
    constraints.extend(christine_constraints)

    # Define the constraints for Helen's schedule
    helen_constraints = []
    for start, end in helen_schedule:
        helen_constraints.extend([
            Not(And(helen_meeting >= start, helen_meeting < 15 * 60)),
            Not(And(helen_meeting >= start, helen_meeting < end)),
            Not(And(meeting_start >= start, meeting_start < end)),
            Not(And(meeting_end > start, meeting_end <= end)),
        ])
    constraints.extend(helen_constraints)

    # Define the constraint for Helen not meeting on Monday after 15:00
    helen_avoid_after_constraints = [
        Not(And(helen_meeting > 15 * 60, helen_meeting <= 17 * 60)),
    ]
    constraints.extend(helen_avoid_after_constraints)

    # Define the solver
    solver = Solver()

    # Add the constraints to the solver
    solver.add(constraints)

    # Solve the solver
    result = solver.check()

    # If the solver found a solution, print the meeting time
    if result == sat:
        model = solver.model()
        print(f"Meeting time: {model[christine_meeting].as_long()} - {model[meeting_end].as_long()}")
    else:
        print("No solution found")

# Example usage
start_time = 9 * 60  # 9:00
end_time = 17 * 60  # 17:00
duration = 30  # 30 minutes
christine_schedule = [(11 * 0, 11 * 30), (15 * 0, 15 * 30)]
helen_schedule = [(9 * 30, 10 * 30), (11 * 0, 11 * 30), (12 * 0, 12 * 30), (13 * 30, 16 * 0), (16 * 30, 17 * 0)]
helen_avoid_after = True

schedule_meeting(start_time, end_time, duration, christine_schedule, helen_schedule, helen_avoid_after)