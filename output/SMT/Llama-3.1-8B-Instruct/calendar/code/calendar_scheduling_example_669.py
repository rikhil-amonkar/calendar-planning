from z3 import *

def schedule_meeting(start_time, end_time, duration, jean_schedule, doris_schedule, doris_avoid_monday_after):
    # Create Z3 variables for the meeting time
    jean_meeting = Int('jean_meeting')
    doris_meeting = Int('doris_meeting')

    # Create Z3 variables for the start and end times of the meeting
    meeting_start = Int('meeting_start')
    meeting_end = Int('meeting_end')

    # Define the constraints for the meeting time
    constraints = [
        And(jean_meeting >= start_time, jean_meeting <= end_time),
        And(doris_meeting >= start_time, doris_meeting <= end_time),
        meeting_start == jean_meeting,
        meeting_end == jean_meeting + duration,
        meeting_start == doris_meeting,
        meeting_end == doris_meeting + duration,
    ]

    # Define the constraints for Jean's schedule
    jean_constraints = []
    for day, schedule in jean_schedule.items():
        for start, end in schedule:
            if day == 'Monday':
                jean_constraints.extend([
                    Not(And(jean_meeting >= start, jean_meeting < end)),
                    Not(And(meeting_start >= start, meeting_start < end)),
                    Not(And(meeting_end > start, meeting_end <= end)),
                ])
            elif day == 'Tuesday':
                jean_constraints.extend([
                    Not(And(jean_meeting >= start, jean_meeting < end)),
                    Not(And(meeting_start >= start, meeting_start < end)),
                    Not(And(meeting_end > start, meeting_end <= end)),
                ])
    constraints.extend(jean_constraints)

    # Define the constraints for Doris's schedule
    doris_constraints = []
    for day, schedule in doris_schedule.items():
        for start, end in schedule:
            if day == 'Monday':
                doris_constraints.extend([
                    Not(And(doris_meeting >= start, doris_meeting < 14 * 60)),
                    Not(And(doris_meeting >= start, doris_meeting < end)),
                    Not(And(meeting_start >= start, meeting_start < end)),
                    Not(And(meeting_end > start, meeting_end <= end)),
                ])
            elif day == 'Tuesday':
                doris_constraints.extend([
                    Not(And(doris_meeting >= start, doris_meeting < end)),
                    Not(And(meeting_start >= start, meeting_start < end)),
                    Not(And(meeting_end > start, meeting_end <= end)),
                ])
    constraints.extend(doris_constraints)

    # Define the constraint for Doris not meeting on Monday after 14:00
    doris_avoid_monday_after_constraints = [
        Not(And(doris_meeting >= 14 * 60, doris_meeting <= 17 * 60)),
    ]
    constraints.extend(doris_avoid_monday_after_constraints)

    # Define the solver
    solver = Solver()

    # Add the constraints to the solver
    solver.add(constraints)

    # Solve the solver
    result = solver.check()

    # If the solver found a solution, print the meeting time
    if result == sat:
        model = solver.model()
        print(f"Meeting time: {model[jean_meeting].as_long()} - {model[meeting_end].as_long()}")
    else:
        print("No solution found")

# Example usage
start_time = 9 * 60  # 9:00
end_time = 17 * 60  # 17:00
duration = 30  # 30 minutes
jean_schedule = {
    'Tuesday': [(11 * 60, 12 * 60), (16 * 60, 16 * 60 + 30)],
}
doris_schedule = {
    'Monday': [(9 * 60, 11 * 60 + 30), (12 * 60, 12 * 60 + 30), (13 * 60 + 30, 16 * 60), (16 * 60 + 30, 17 * 60)],
    'Tuesday': [(9 * 60, 17 * 60)],
}
doris_avoid_monday_after = True

schedule_meeting(start_time, end_time, duration, jean_schedule, doris_schedule, doris_avoid_monday_after)