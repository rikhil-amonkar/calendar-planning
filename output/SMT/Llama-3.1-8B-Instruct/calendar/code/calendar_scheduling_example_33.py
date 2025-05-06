from z3 import *

def schedule_meeting(start_time, end_time, duration, lisa_schedule, bobby_schedule, randy_schedule, bobby_avoid_after):
    # Create Z3 variables for the meeting time
    lisa_meeting = Int('lisa_meeting')
    bobby_meeting = Int('bobby_meeting')
    randy_meeting = Int('randy_meeting')

    # Create Z3 variables for the start and end times of the meeting
    meeting_start = Int('meeting_start')
    meeting_end = Int('meeting_end')

    # Define the constraints for the meeting time
    constraints = [
        And(lisa_meeting >= start_time, lisa_meeting <= end_time),
        And(bobby_meeting >= start_time, bobby_meeting <= end_time),
        And(randy_meeting >= start_time, randy_meeting <= end_time),
        meeting_start == lisa_meeting,
        meeting_end == lisa_meeting + duration,
        meeting_start == bobby_meeting,
        meeting_end == bobby_meeting + duration,
        meeting_start == randy_meeting,
        meeting_end == randy_meeting + duration,
    ]

    # Define the constraints for Lisa's schedule
    lisa_constraints = []
    for start, end in lisa_schedule:
        lisa_constraints.extend([
            Not(And(lisa_meeting >= start, lisa_meeting < end)),
            Not(And(meeting_start >= start, meeting_start < end)),
            Not(And(meeting_end > start, meeting_end <= end)),
        ])
    constraints.extend(lisa_constraints)

    # Define the constraints for Bobby's schedule
    bobby_constraints = []
    for start, end in bobby_schedule:
        bobby_constraints.extend([
            Not(And(bobby_meeting >= start, bobby_meeting < end)),
            Not(And(meeting_start >= start, meeting_start < end)),
            Not(And(meeting_end > start, meeting_end <= end)),
        ])
    constraints.extend(bobby_constraints)

    # Define the constraints for Randy's schedule
    randy_constraints = []
    for start, end in randy_schedule:
        randy_constraints.extend([
            Not(And(randy_meeting >= start, randy_meeting < end)),
            Not(And(meeting_start >= start, meeting_start < end)),
            Not(And(meeting_end > start, meeting_end <= end)),
        ])
    constraints.extend(randy_constraints)

    # Define the constraint for Bobby avoiding meetings on Monday after 15:00
    bobby_avoid_after_constraints = [
        Not(And(bobby_meeting > 15 * 60, bobby_meeting <= 17 * 60)),
    ]
    constraints.extend(bobby_avoid_after_constraints)

    # Define the solver
    solver = Solver()

    # Add the constraints to the solver
    solver.add(constraints)

    # Solve the solver
    result = solver.check()

    # If the solver found a solution, print the meeting time
    if result == sat:
        model = solver.model()
        print(f"Meeting time: {model[bobby_meeting].as_long()} - {model[meeting_end].as_long()}")
    else:
        print("No solution found")

# Example usage
start_time = 9 * 60  # 9:00
end_time = 17 * 60  # 17:00
duration = 30  # 30 minutes
lisa_schedule = [(9 * 60, 10 * 60), (10 * 60 + 30, 11 * 60 + 30), (12 * 60 + 30, 13 * 60), (16 * 60, 16 * 60 + 30)]
bobby_schedule = [(9 * 60, 9 * 60 + 30), (10 * 60, 10 * 60 + 30), (11 * 60, 12 * 60), (15 * 60, 15 * 60 + 30)]
randy_schedule = [(9 * 60 + 30, 10 * 60), (10 * 60 + 30, 11 * 60), (11 * 60 + 30, 12 * 60 + 30), (13 * 60, 13 * 60 + 30), (14 * 60 + 30, 15 * 60 + 30), (16 * 60, 16 * 60 + 30)]
bobby_avoid_after = True

schedule_meeting(start_time, end_time, duration, lisa_schedule, bobby_schedule, randy_schedule, bobby_avoid_after)