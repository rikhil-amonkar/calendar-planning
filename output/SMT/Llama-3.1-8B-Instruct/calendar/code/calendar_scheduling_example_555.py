from z3 import *

def schedule_meeting(start_time, end_time, duration, evelyn_schedule, randy_schedule, evelyn_avoid_after):
    # Create Z3 variables for the meeting time
    evelyn_meeting = Int('evelyn_meeting')
    randy_meeting = Int('randy_meeting')

    # Create Z3 variables for the start and end times of the meeting
    meeting_start = Int('meeting_start')
    meeting_end = Int('meeting_end')

    # Define the constraints for the meeting time
    constraints = [
        And(evelyn_meeting >= start_time, evelyn_meeting <= end_time),
        And(randy_meeting >= start_time, randy_meeting <= end_time),
        meeting_start == evelyn_meeting,
        meeting_end == evelyn_meeting + duration,
        meeting_start == randy_meeting,
        meeting_end == randy_meeting + duration,
    ]

    # Define the constraints for Evelyn's schedule
    evelyn_constraints = []
    for start, end in evelyn_schedule:
        evelyn_constraints.extend([
            Not(And(evelyn_meeting >= start, evelyn_meeting < end)),
            Not(And(meeting_start >= start, meeting_start < end)),
            Not(And(meeting_end > start, meeting_end <= end)),
        ])
    constraints.extend(evelyn_constraints)

    # Define the constraints for Randy's schedule
    randy_constraints = []
    for start, end in randy_schedule:
        randy_constraints.extend([
            Not(And(randy_meeting >= start, randy_meeting < end)),
            Not(And(meeting_start >= start, meeting_start < end)),
            Not(And(meeting_end > start, meeting_end <= end)),
        ])
    constraints.extend(randy_constraints)

    # Define the constraint for Evelyn not meeting on Monday after 13:00
    evelyn_avoid_after_constraints = [
        Not(And(evelyn_meeting > 13 * 0, evelyn_meeting <= 17 * 60)),
    ]
    constraints.extend(evelyn_avoid_after_constraints)

    # Define the solver
    solver = Solver()

    # Add the constraints to the solver
    solver.add(constraints)

    # Solve the solver
    result = solver.check()

    # If the solver found a solution, print the meeting time
    if result == sat:
        model = solver.model()
        print(f"Meeting time: {model[evelyn_meeting].as_long()} - {model[meeting_end].as_long()}")
    else:
        print("No solution found")

# Example usage
start_time = 9 * 60  # 9:00
end_time = 17 * 60  # 17:00
duration = 30  # 30 minutes
evelyn_schedule = []
randy_schedule = [(9 * 0, 10 * 30), (11 * 0, 15 * 30), (16 * 0, 17 * 0)]
evelyn_avoid_after = True

schedule_meeting(start_time, end_time, duration, evelyn_schedule, randy_schedule, evelyn_avoid_after)