from z3 import *

def schedule_meeting(start_time, end_time, duration, emily_schedule, melissa_schedule, frank_schedule, frank_avoid_after):
    # Create Z3 variables for the meeting time
    emily_meeting = Int('emily_meeting')
    melissa_meeting = Int('melissa_meeting')
    frank_meeting = Int('frank_meeting')

    # Create Z3 variables for the start and end times of the meeting
    meeting_start = Int('meeting_start')
    meeting_end = Int('meeting_end')

    # Define the constraints for the meeting time
    constraints = [
        And(emily_meeting >= start_time, emily_meeting <= end_time),
        And(melissa_meeting >= start_time, melissa_meeting <= end_time),
        And(frank_meeting >= start_time, frank_meeting <= end_time),
        meeting_start == emily_meeting,
        meeting_end == emily_meeting + duration,
        meeting_start == melissa_meeting,
        meeting_end == melissa_meeting + duration,
        meeting_start == frank_meeting,
        meeting_end == frank_meeting + duration,
    ]

    # Define the constraints for Emily's schedule
    emily_constraints = []
    for start, end in emily_schedule:
        emily_constraints.extend([
            Not(And(emily_meeting >= start, emily_meeting < end)),
            Not(And(meeting_start >= start, meeting_start < end)),
            Not(And(meeting_end > start, meeting_end <= end)),
        ])
    constraints.extend(emily_constraints)

    # Define the constraints for Melissa's schedule
    melissa_constraints = []
    for start, end in melissa_schedule:
        melissa_constraints.extend([
            Not(And(melissa_meeting >= start, melissa_meeting < end)),
            Not(And(meeting_start >= start, meeting_start < end)),
            Not(And(meeting_end > start, meeting_end <= end)),
        ])
    constraints.extend(melissa_constraints)

    # Define the constraints for Frank's schedule
    frank_constraints = []
    for start, end in frank_schedule:
        frank_constraints.extend([
            Not(And(frank_meeting >= start, frank_meeting < 9 * 60 + 30)),
            Not(And(frank_meeting >= start, frank_meeting < end)),
            Not(And(meeting_start >= start, meeting_start < end)),
            Not(And(meeting_end > start, meeting_end <= end)),
        ])
    constraints.extend(frank_constraints)

    # Define the constraint for Frank not meeting on Monday after 9:30
    frank_avoid_after_constraints = [
        Not(And(frank_meeting > 9 * 60 + 30, frank_meeting <= 17 * 60)),
    ]
    constraints.extend(frank_avoid_after_constraints)

    # Define the solver
    solver = Solver()

    # Add the constraints to the solver
    solver.add(constraints)

    # Solve the solver
    result = solver.check()

    # If the solver found a solution, print the meeting time
    if result == sat:
        model = solver.model()
        print(f"Meeting time: {model[emily_meeting].as_long()} - {model[meeting_end].as_long()}")
    else:
        print("No solution found")

# Example usage
start_time = 9 * 60  # 9:00
end_time = 17 * 60  # 17:00
duration = 30  # 30 minutes
emily_schedule = [(10 * 60, 10 * 60 + 30), (11 * 60 + 30, 12 * 60 + 30), (14 * 60, 15 * 60), (16 * 60, 16 * 60 + 30)]
melissa_schedule = [(9 * 60 + 30, 10 * 60), (14 * 60 + 30, 15 * 60)]
frank_schedule = [(10 * 60, 10 * 60 + 30), (11 * 60, 11 * 60 + 30), (12 * 60 + 30, 13 * 60), (13 * 60 + 30, 14 * 60 + 30), (15 * 60, 16 * 60), (16 * 60 + 30, 17 * 60)]
frank_avoid_after = True

schedule_meeting(start_time, end_time, duration, emily_schedule, melissa_schedule, frank_schedule, frank_avoid_after)