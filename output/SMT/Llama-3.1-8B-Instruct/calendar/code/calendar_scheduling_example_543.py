from z3 import *

def schedule_meeting(start_time, end_time, duration, james_schedule, john_schedule):
    # Create Z3 variables for the meeting time
    james_meeting = Int('james_meeting')
    john_meeting = Int('john_meeting')

    # Create Z3 variables for the start and end times of the meeting
    meeting_start = Int('meeting_start')
    meeting_end = Int('meeting_end')

    # Define the constraints for the meeting time
    constraints = [
        And(james_meeting >= start_time, james_meeting <= end_time),
        And(john_meeting >= start_time, john_meeting <= end_time),
        meeting_start == james_meeting,
        meeting_end == james_meeting + duration,
        meeting_start == john_meeting,
        meeting_end == john_meeting + duration,
    ]

    # Define the constraints for James' schedule
    james_constraints = []
    for start, end in james_schedule:
        james_constraints.extend([
            Not(And(james_meeting >= start, james_meeting < end)),
            Not(And(meeting_start >= start, meeting_start < end)),
            Not(And(meeting_end > start, meeting_end <= end)),
        ])
    constraints.extend(james_constraints)

    # Define the constraints for John's schedule
    john_constraints = []
    for start, end in john_schedule:
        john_constraints.extend([
            Not(And(john_meeting >= start, john_meeting < end)),
            Not(And(meeting_start >= start, meeting_start < end)),
            Not(And(meeting_end > start, meeting_end <= end)),
        ])
    constraints.extend(john_constraints)

    # Define the solver
    solver = Solver()

    # Add the constraints to the solver
    solver.add(constraints)

    # Solve the solver
    result = solver.check()

    # If the solver found a solution, print the meeting time
    if result == sat:
        model = solver.model()
        print(f"Meeting time: {model[james_meeting].as_long()} - {model[meeting_end].as_long()}")
    else:
        print("No solution found")

# Example usage
start_time = 9 * 60  # 9:00
end_time = 17 * 60  # 17:00
duration = 60  # 1 hour
james_schedule = [(11 * 60 + 30, 12 * 60), (14 * 60 + 30, 15 * 60)]
john_schedule = [(9 * 60 + 30, 11 * 60), (11 * 60 + 30, 12 * 60), (12 * 60 + 30, 13 * 60 + 30), (14 * 60 + 30, 16 * 60 + 30)]

schedule_meeting(start_time, end_time, duration, james_schedule, john_schedule)