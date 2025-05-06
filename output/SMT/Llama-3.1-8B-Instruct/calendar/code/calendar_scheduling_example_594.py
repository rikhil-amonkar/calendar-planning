from z3 import *

def schedule_meeting(start_time, end_time, duration, adam_schedule, roy_schedule):
    # Create Z3 variables for the meeting time
    adam_meeting = Int('adam_meeting')
    roy_meeting = Int('roy_meeting')

    # Create Z3 variables for the start and end times of the meeting
    meeting_start = Int('meeting_start')
    meeting_end = Int('meeting_end')

    # Define the constraints for the meeting time
    constraints = [
        And(adam_meeting >= start_time, adam_meeting <= end_time),
        And(roy_meeting >= start_time, roy_meeting <= end_time),
        meeting_start == adam_meeting,
        meeting_end == adam_meeting + duration,
        meeting_start == roy_meeting,
        meeting_end == roy_meeting + duration,
    ]

    # Define the constraints for Adam's schedule
    adam_constraints = []
    for start, end in adam_schedule:
        adam_constraints.extend([
            Not(And(adam_meeting >= start, adam_meeting < end)),
            Not(And(meeting_start >= start, meeting_start < end)),
            Not(And(meeting_end > start, meeting_end <= end)),
        ])
    constraints.extend(adam_constraints)

    # Define the constraints for Roy's schedule
    roy_constraints = []
    for start, end in roy_schedule:
        roy_constraints.extend([
            Not(And(roy_meeting >= start, roy_meeting < end)),
            Not(And(meeting_start >= start, meeting_start < end)),
            Not(And(meeting_end > start, meeting_end <= end)),
        ])
    constraints.extend(roy_constraints)

    # Define the solver
    solver = Solver()

    # Add the constraints to the solver
    solver.add(constraints)

    # Solve the solver
    result = solver.check()

    # If the solver found a solution, print the meeting time
    if result == sat:
        model = solver.model()
        print(f"Meeting time: {model[adam_meeting].as_long()} - {model[meeting_end].as_long()}")
    else:
        print("No solution found")

# Example usage
start_time = 9 * 60  # 9:00
end_time = 17 * 60  # 17:00
duration = 30  # 30 minutes
adam_schedule = [(9 * 30, 10 * 0), (12 * 30, 13 * 0), (14 * 30, 15 * 0), (16 * 30, 17 * 0)]
roy_schedule = [(10 * 0, 11 * 0), (11 * 30, 13 * 0), (13 * 30, 14 * 30), (16 * 30, 17 * 0)]

schedule_meeting(start_time, end_time, duration, adam_schedule, roy_schedule)