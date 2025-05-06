from z3 import *

def schedule_meeting(start_time, end_time, duration, kayla_schedule, rebecca_schedule):
    # Create Z3 variables for the meeting time
    kayla_meeting = Int('kayla_meeting')
    rebecca_meeting = Int('rebecca_meeting')

    # Create Z3 variables for the start and end times of the meeting
    meeting_start = Int('meeting_start')
    meeting_end = Int('meeting_end')

    # Define the constraints for the meeting time
    constraints = [
        And(kayla_meeting >= start_time, kayla_meeting <= end_time),
        And(rebecca_meeting >= start_time, rebecca_meeting <= end_time),
        meeting_start == kayla_meeting,
        meeting_end == kayla_meeting + duration,
        meeting_start == rebecca_meeting,
        meeting_end == rebecca_meeting + duration,
    ]

    # Define the constraints for Kayla's schedule
    kayla_constraints = []
    for start, end in kayla_schedule:
        kayla_constraints.extend([
            Not(And(kayla_meeting >= start, kayla_meeting < end)),
            Not(And(meeting_start >= start, meeting_start < end)),
            Not(And(meeting_end > start, meeting_end <= end)),
        ])
    constraints.extend(kayla_constraints)

    # Define the constraints for Rebecca's schedule
    rebecca_constraints = []
    for start, end in rebecca_schedule:
        rebecca_constraints.extend([
            Not(And(rebecca_meeting >= start, rebecca_meeting < end)),
            Not(And(meeting_start >= start, meeting_start < end)),
            Not(And(meeting_end > start, meeting_end <= end)),
        ])
    constraints.extend(rebecca_constraints)

    # Define the solver
    solver = Solver()

    # Add the constraints to the solver
    solver.add(constraints)

    # Solve the solver
    result = solver.check()

    # If the solver found a solution, print the meeting time
    if result == sat:
        model = solver.model()
        print(f"Meeting time: {model[kayla_meeting].as_long()} - {model[meeting_end].as_long()}")
    else:
        print("No solution found")

# Example usage
start_time = 9 * 60  # 9:00
end_time = 17 * 60  # 17:00
duration = 60  # 1 hour
kayla_schedule = [(10 * 0, 10 * 30), (14 * 30, 16 * 0)]
rebecca_schedule = [(9 * 0, 13 * 0), (13 * 30, 15 * 0), (15 * 30, 16 * 0)]

schedule_meeting(start_time, end_time, duration, kayla_schedule, rebecca_schedule)