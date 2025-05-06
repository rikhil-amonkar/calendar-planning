from z3 import *

def schedule_meeting(start_time, end_time, duration, jack_schedule, charlotte_schedule, jack_avoid_after):
    # Create Z3 variables for the meeting time
    jack_meeting = Int('jack_meeting')
    charlotte_meeting = Int('charlotte_meeting')

    # Create Z3 variables for the start and end times of the meeting
    meeting_start = Int('meeting_start')
    meeting_end = Int('meeting_end')

    # Define the constraints for the meeting time
    constraints = [
        And(jack_meeting >= start_time, jack_meeting <= end_time),
        And(charlotte_meeting >= start_time, charlotte_meeting <= end_time),
        meeting_start == jack_meeting,
        meeting_end == jack_meeting + duration,
        meeting_start == charlotte_meeting,
        meeting_end == charlotte_meeting + duration,
    ]

    # Define the constraints for Jack's schedule
    jack_constraints = []
    for start, end in jack_schedule:
        jack_constraints.extend([
            Not(And(jack_meeting >= start, jack_meeting < end)),
            Not(And(meeting_start >= start, meeting_start < end)),
            Not(And(meeting_end > start, meeting_end <= end)),
        ])
    constraints.extend(jack_constraints)

    # Define the constraints for Charlotte's schedule
    charlotte_constraints = []
    for start, end in charlotte_schedule:
        charlotte_constraints.extend([
            Not(And(charlotte_meeting >= start, charlotte_meeting < end)),
            Not(And(meeting_start >= start, meeting_start < end)),
            Not(And(meeting_end > start, meeting_end <= end)),
        ])
    constraints.extend(charlotte_constraints)

    # Define the constraints for Jack avoiding more meetings after 12:30
    jack_avoid_after_constraints = [
        Not(And(jack_meeting > 12 * 60, jack_meeting <= 17 * 60)),
    ]
    constraints.extend(jack_avoid_after_constraints)

    # Define the solver
    solver = Solver()

    # Add the constraints to the solver
    solver.add(constraints)

    # Solve the solver
    result = solver.check()

    # If the solver found a solution, print the meeting time
    if result == sat:
        model = solver.model()
        print(f"Meeting time: {model[jack_meeting].as_long()} - {model[meeting_end].as_long()}")
    else:
        print("No solution found")

# Example usage
start_time = 9 * 60  # 9:00
end_time = 17 * 60  # 17:00
duration = 30  # 30 minutes
jack_schedule = [(9 * 60 + 30, 10 * 60), (11 * 60, 11 * 60 + 30), (12 * 60 + 30, 13 * 60), (14 * 60, 14 * 60 + 30), (16 * 60, 16 * 60 + 30)]
charlotte_schedule = [(9 * 60 + 30, 10 * 60), (10 * 60 + 30, 12 * 60), (12 * 60 + 30, 13 * 60 + 30), (14 * 60, 16 * 60)]
jack_avoid_after = True

schedule_meeting(start_time, end_time, duration, jack_schedule, charlotte_schedule, jack_avoid_after)