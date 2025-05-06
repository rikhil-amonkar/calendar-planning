from z3 import *

def schedule_meeting(start_time, end_time, duration, jesse_schedule, lawrence_schedule, lawrence_avoid_after):
    # Create Z3 variables for the meeting time
    jesse_meeting = Int('jesse_meeting')
    lawrence_meeting = Int('lawrence_meeting')

    # Create Z3 variables for the start and end times of the meeting
    meeting_start = Int('meeting_start')
    meeting_end = Int('meeting_end')

    # Define the constraints for the meeting time
    constraints = [
        And(jesse_meeting >= start_time, jesse_meeting <= end_time),
        And(lawrence_meeting >= start_time, lawrence_meeting <= end_time),
        meeting_start == jesse_meeting,
        meeting_end == jesse_meeting + duration,
        meeting_start == lawrence_meeting,
        meeting_end == lawrence_meeting + duration,
    ]

    # Define the constraints for Jesse's schedule
    jesse_constraints = []
    for day, schedule in jesse_schedule.items():
        for start, end in schedule:
            if day == 'Monday':
                jesse_constraints.extend([
                    Not(And(jesse_meeting >= start, jesse_meeting < end)),
                    Not(And(meeting_start >= start, meeting_start < end)),
                    Not(And(meeting_end > start, meeting_end <= end)),
                ])
            elif day == 'Tuesday':
                jesse_constraints.extend([
                    Not(And(jesse_meeting >= start, jesse_meeting < end)),
                    Not(And(meeting_start >= start, meeting_start < end)),
                    Not(And(meeting_end > start, meeting_end <= end)),
                ])
    constraints.extend(jesse_constraints)

    # Define the constraints for Lawrence's schedule
    lawrence_constraints = []
    for day, schedule in lawrence_schedule.items():
        for start, end in schedule:
            if day == 'Monday':
                lawrence_constraints.extend([
                    Not(And(lawrence_meeting >= start, lawrence_meeting < end)),
                    Not(And(meeting_start >= start, meeting_start < end)),
                    Not(And(meeting_end > start, meeting_end <= end)),
                ])
            elif day == 'Tuesday':
                lawrence_constraints.extend([
                    Not(And(lawrence_meeting >= start, lawrence_meeting < 16 * 60 + 30)),
                    Not(And(lawrence_meeting >= start, lawrence_meeting < end)),
                    Not(And(meeting_start >= start, meeting_start < end)),
                    Not(And(meeting_end > start, meeting_end <= end)),
                ])
    constraints.extend(lawrence_constraints)

    # Define the constraint for Lawrence not meeting on Tuesday after 16:30
    lawrence_avoid_after_constraints = [
        Not(And(lawrence_meeting > 16 * 60, lawrence_meeting <= 17 * 60)),
    ]
    constraints.extend(lawrence_avoid_after_constraints)

    # Define the solver
    solver = Solver()

    # Add the constraints to the solver
    solver.add(constraints)

    # Solve the solver
    result = solver.check()

    # If the solver found a solution, print the meeting time
    if result == sat:
        model = solver.model()
        print(f"Meeting time: {model[jesse_meeting].as_long()} - {model[meeting_end].as_long()}")
    else:
        print("No solution found")

# Example usage
start_time = 9 * 60  # 9:00
end_time = 17 * 60  # 17:00
duration = 30  # 30 minutes
jesse_schedule = {
    'Monday': [(13 * 60 + 30, 14 * 60), (14 * 60 + 30, 15 * 60)],
    'Tuesday': [(9 * 60, 9 * 60 + 30), (13 * 60, 13 * 60 + 30), (14 * 60, 15 * 60)],
}
lawrence_schedule = {
    'Monday': [(9 * 60, 17 * 60)],
    'Tuesday': [(9 * 60 + 30, 10 * 60 + 30), (11 * 60 + 30, 12 * 60 + 30), (13 * 60, 13 * 60 + 30), (14 * 60 + 30, 15 * 60), (15 * 60 + 30, 16 * 60 + 30)],
}
lawrence_avoid_after = True

schedule_meeting(start_time, end_time, duration, jesse_schedule, lawrence_schedule, lawrence_avoid_after)