from z3 import *

def schedule_meeting(start_time, end_time, duration, raymond_schedule, billy_schedule, donald_schedule, billy_avoid_after):
    # Create Z3 variables for the meeting time
    raymond_meeting = Int('raymond_meeting')
    billy_meeting = Int('billy_meeting')
    donald_meeting = Int('donald_meeting')

    # Create Z3 variables for the start and end times of the meeting
    meeting_start = Int('meeting_start')
    meeting_end = Int('meeting_end')

    # Define the constraints for the meeting time
    constraints = [
        And(raymond_meeting >= start_time, raymond_meeting <= end_time),
        And(billy_meeting >= start_time, billy_meeting <= end_time),
        And(donald_meeting >= start_time, donald_meeting <= end_time),
        meeting_start == raymond_meeting,
        meeting_end == raymond_meeting + duration,
        meeting_start == billy_meeting,
        meeting_end == billy_meeting + duration,
        meeting_start == donald_meeting,
        meeting_end == donald_meeting + duration,
    ]

    # Define the constraints for Raymond's schedule
    raymond_constraints = []
    for start, end in raymond_schedule:
        raymond_constraints.extend([
            Not(And(raymond_meeting >= start, raymond_meeting < end)),
            Not(And(meeting_start >= start, meeting_start < end)),
            Not(And(meeting_end > start, meeting_end <= end)),
        ])
    constraints.extend(raymond_constraints)

    # Define the constraints for Billy's schedule
    billy_constraints = []
    for start, end in billy_schedule:
        billy_constraints.extend([
            Not(And(billy_meeting >= start, billy_meeting < end)),
            Not(And(meeting_start >= start, meeting_start < end)),
            Not(And(meeting_end > start, meeting_end <= end)),
        ])
    constraints.extend(billy_constraints)

    # Define the constraints for Donald's schedule
    donald_constraints = []
    for start, end in donald_schedule:
        donald_constraints.extend([
            Not(And(donald_meeting >= start, donald_meeting < end)),
            Not(And(meeting_start >= start, meeting_start < end)),
            Not(And(meeting_end > start, meeting_end <= end)),
        ])
    constraints.extend(donald_constraints)

    # Define the constraint for Billy avoiding meetings on Monday after 15:00
    billy_avoid_after_constraints = [
        Not(And(billy_meeting > 15 * 60, billy_meeting <= 17 * 60)),
    ]
    constraints.extend(billy_avoid_after_constraints)

    # Define the solver
    solver = Solver()

    # Add the constraints to the solver
    solver.add(constraints)

    # Solve the solver
    result = solver.check()

    # If the solver found a solution, print the meeting time
    if result == sat:
        model = solver.model()
        print(f"Meeting time: {model[billy_meeting].as_long()} - {model[meeting_end].as_long()}")
    else:
        print("No solution found")

# Example usage
start_time = 9 * 60  # 9:00
end_time = 17 * 60  # 17:00
duration = 30  # 30 minutes
raymond_schedule = [(9 * 60, 9 * 60 + 30), (11 * 60 + 30, 12 * 60), (13 * 60, 13 * 60 + 30), (15 * 60, 15 * 60 + 30)]
billy_schedule = [(10 * 60, 10 * 60 + 30), (12 * 60, 13 * 60), (16 * 60 + 30, 17 * 60)]
donald_schedule = [(9 * 60, 9 * 60 + 30), (10 * 60, 11 * 60), (12 * 60, 13 * 60), (14 * 60, 14 * 60 + 30), (16 * 60, 17 * 60)]
billy_avoid_after = True

schedule_meeting(start_time, end_time, duration, raymond_schedule, billy_schedule, donald_schedule, billy_avoid_after)