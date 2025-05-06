from z3 import *

def schedule_meeting(start_time, end_time, duration, eric_schedule, henry_schedule, henry_avoid_after):
    # Create Z3 variables for the meeting time
    eric_meeting = Int('eric_meeting')
    henry_meeting = Int('henry_meeting')

    # Create Z3 variables for the start and end times of the meeting
    meeting_start = Int('meeting_start')
    meeting_end = Int('meeting_end')

    # Define the constraints for the meeting time
    constraints = [
        And(eric_meeting >= start_time, eric_meeting <= end_time),
        And(henry_meeting >= start_time, henry_meeting <= end_time),
        meeting_start == eric_meeting,
        meeting_end == eric_meeting + duration,
        meeting_start == henry_meeting,
        meeting_end == henry_meeting + duration,
    ]

    # Define the constraints for Eric's schedule
    eric_constraints = []
    for start, end in eric_schedule:
        eric_constraints.extend([
            Not(And(eric_meeting >= start, eric_meeting < end)),
            Not(And(meeting_start >= start, meeting_start < end)),
            Not(And(meeting_end > start, meeting_end <= end)),
        ])
    constraints.extend(eric_constraints)

    # Define the constraints for Henry's schedule
    henry_constraints = []
    for start, end in henry_schedule:
        henry_constraints.extend([
            Not(And(henry_meeting >= start, henry_meeting < 10 * 0)),
            Not(And(henry_meeting >= start, henry_meeting < end)),
            Not(And(meeting_start >= start, meeting_start < end)),
            Not(And(meeting_end > start, meeting_end <= end)),
        ])
    constraints.extend(henry_constraints)

    # Define the constraint for Henry not meeting on Monday after 10:00
    henry_avoid_after_constraints = [
        Not(And(henry_meeting > 10 * 0, henry_meeting <= 17 * 60)),
    ]
    constraints.extend(henry_avoid_after_constraints)

    # Define the solver
    solver = Solver()

    # Add the constraints to the solver
    solver.add(constraints)

    # Solve the solver
    result = solver.check()

    # If the solver found a solution, print the meeting time
    if result == sat:
        model = solver.model()
        print(f"Meeting time: {model[eric_meeting].as_long()} - {model[meeting_end].as_long()}")
    else:
        print("No solution found")

# Example usage
start_time = 9 * 60  # 9:00
end_time = 17 * 60  # 17:00
duration = 30  # 30 minutes
eric_schedule = [(12 * 0, 13 * 0), (14 * 0, 15 * 0)]
henry_schedule = [(9 * 30, 10 * 0), (10 * 30, 11 * 0), (11 * 30, 12 * 30), (13 * 0, 13 * 30), (14 * 30, 15 * 0), (16 * 0, 17 * 0)]
henry_avoid_after = True

schedule_meeting(start_time, end_time, duration, eric_schedule, henry_schedule, henry_avoid_after)