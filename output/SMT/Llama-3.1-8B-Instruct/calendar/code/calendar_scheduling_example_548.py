from z3 import *

def schedule_meeting(start_time, end_time, duration, judy_schedule, nicole_schedule, nicole_prefer_after):
    # Create Z3 variables for the meeting time
    judy_meeting = Int('judy_meeting')
    nicole_meeting = Int('nicole_meeting')

    # Create Z3 variables for the start and end times of the meeting
    meeting_start = Int('meeting_start')
    meeting_end = Int('meeting_end')

    # Define the constraints for the meeting time
    constraints = [
        And(judy_meeting >= start_time, judy_meeting <= end_time),
        And(nicole_meeting >= start_time, nicole_meeting <= end_time),
        meeting_start == judy_meeting,
        meeting_end == judy_meeting + duration,
        meeting_start == nicole_meeting,
        meeting_end == nicole_meeting + duration,
    ]

    # Define the constraints for Judy's schedule
    judy_constraints = []
    for start, end in judy_schedule:
        judy_constraints.extend([
            Not(And(judy_meeting >= start, judy_meeting < end)),
            Not(And(meeting_start >= start, meeting_start < end)),
            Not(And(meeting_end > start, meeting_end <= end)),
        ])
    constraints.extend(judy_constraints)

    # Define the constraints for Nicole's schedule
    nicole_constraints = []
    for start, end in nicole_schedule:
        nicole_constraints.extend([
            Not(And(nicole_meeting >= start, nicole_meeting < end)),
            Not(And(meeting_start >= start, meeting_start < end)),
            Not(And(meeting_end > start, meeting_end <= end)),
        ])
    constraints.extend(nicole_constraints)

    # Define the constraint for Nicole preferring to meet after 16:00
    nicole_prefer_after_constraints = [
        Not(And(nicole_meeting >= 16 * 60, nicole_meeting < 17 * 60)),
    ]
    constraints.extend(nicole_prefer_after_constraints)

    # Define the solver
    solver = Solver()

    # Add the constraints to the solver
    solver.add(constraints)

    # Solve the solver
    result = solver.check()

    # If the solver found a solution, print the meeting time
    if result == sat:
        model = solver.model()
        print(f"Meeting time: {model[judy_meeting].as_long()} - {model[meeting_end].as_long()}")
    else:
        print("No solution found")

# Example usage
start_time = 9 * 60  # 9:00
end_time = 17 * 60  # 17:00
duration = 30  # 30 minutes
judy_schedule = []
nicole_schedule = [(9 * 60, 10 * 60), (10 * 60 + 30, 16 * 60 + 30)]
nicole_prefer_after = True

schedule_meeting(start_time, end_time, duration, judy_schedule, nicole_schedule, nicole_prefer_after)