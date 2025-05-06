from z3 import *

def schedule_meeting(start_time, end_time, duration, margaret_schedule, donna_schedule, helen_schedule, helen_avoid_after):
    # Create Z3 variables for the meeting time
    margaret_meeting = Int('margaret_meeting')
    donna_meeting = Int('donna_meeting')
    helen_meeting = Int('helen_meeting')

    # Create Z3 variables for the start and end times of the meeting
    meeting_start = Int('meeting_start')
    meeting_end = Int('meeting_end')

    # Define the constraints for the meeting time
    constraints = [
        And(margaret_meeting >= start_time, margaret_meeting <= end_time),
        And(donna_meeting >= start_time, donna_meeting <= end_time),
        And(helen_meeting >= start_time, helen_meeting <= end_time),
        meeting_start == margaret_meeting,
        meeting_end == margaret_meeting + duration,
        meeting_start == donna_meeting,
        meeting_end == donna_meeting + duration,
        meeting_start == helen_meeting,
        meeting_end == helen_meeting + duration,
    ]

    # Define the constraints for Margaret's schedule
    margaret_constraints = []
    for start, end in margaret_schedule:
        margaret_constraints.extend([
            Not(And(margaret_meeting >= start, margaret_meeting < end)),
            Not(And(meeting_start >= start, meeting_start < end)),
            Not(And(meeting_end > start, meeting_end <= end)),
        ])
    constraints.extend(margaret_constraints)

    # Define the constraints for Donna's schedule
    donna_constraints = []
    for start, end in donna_schedule:
        donna_constraints.extend([
            Not(And(donna_meeting >= start, donna_meeting < end)),
            Not(And(meeting_start >= start, meeting_start < end)),
            Not(And(meeting_end > start, meeting_end <= end)),
        ])
    constraints.extend(donna_constraints)

    # Define the constraints for Helen's schedule
    helen_constraints = []
    for start, end in helen_schedule:
        helen_constraints.extend([
            Not(And(helen_meeting >= start, helen_meeting < end)),
            Not(And(meeting_start >= start, meeting_start < end)),
            Not(And(meeting_end > start, meeting_end <= end)),
        ])
    constraints.extend(helen_constraints)

    # Define the constraint for Helen not meeting on Monday after 13:30
    helen_avoid_after_constraints = [
        Not(And(helen_meeting > 13 * 60, helen_meeting <= 17 * 60)),
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
        print(f"Meeting time: {model[margaret_meeting].as_long()} - {model[meeting_end].as_long()}")
    else:
        print("No solution found")

# Example usage
start_time = 9 * 60  # 9:00
end_time = 17 * 60  # 17:00
duration = 30  # 30 minutes
margaret_schedule = [(9 * 60, 10 * 60), (10 * 60 + 30, 11 * 60), (11 * 60 + 30, 12 * 60), (13 * 60, 13 * 60 + 30), (15 * 60, 15 * 60 + 30)]
donna_schedule = [(14 * 60 + 30, 15 * 60), (16 * 60, 16 * 60 + 30)]
helen_schedule = [(9 * 60, 9 * 60 + 30), (10 * 60, 11 * 60 + 30), (13 * 60, 14 * 60), (14 * 60 + 30, 15 * 60), (15 * 60 + 30, 17 * 60)]
helen_avoid_after = True

schedule_meeting(start_time, end_time, duration, margaret_schedule, donna_schedule, helen_schedule, helen_avoid_after)