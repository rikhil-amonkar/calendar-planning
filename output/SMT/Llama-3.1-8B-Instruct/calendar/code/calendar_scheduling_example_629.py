from z3 import *

def schedule_meeting(start_time, end_time, duration, margaret_schedule, alexis_schedule, margaret_avoid_monday, margaret_avoid_tuesday_before):
    # Create Z3 variables for the meeting time
    margaret_meeting = Int('margaret_meeting')
    alexis_meeting = Int('alexis_meeting')

    # Create Z3 variables for the start and end times of the meeting
    meeting_start = Int('meeting_start')
    meeting_end = Int('meeting_end')

    # Define the constraints for the meeting time
    constraints = [
        And(margaret_meeting >= start_time, margaret_meeting <= end_time),
        And(alexis_meeting >= start_time, alexis_meeting <= end_time),
        meeting_start == margaret_meeting,
        meeting_end == margaret_meeting + duration,
        meeting_start == alexis_meeting,
        meeting_end == alexis_meeting + duration,
    ]

    # Define the constraints for Margaret's schedule
    margaret_constraints = []
    for day, schedule in margaret_schedule.items():
        for start, end in schedule:
            if day == 'Monday':
                margaret_constraints.extend([
                    Not(And(margaret_meeting >= start, margaret_meeting < end)),
                    Not(And(meeting_start >= start, meeting_start < end)),
                    Not(And(meeting_end > start, meeting_end <= end)),
                ])
            elif day == 'Tuesday':
                margaret_constraints.extend([
                    Not(And(margaret_meeting >= start, margaret_meeting < 14 * 60 + 30)),
                    Not(And(margaret_meeting >= start, margaret_meeting < end)),
                    Not(And(meeting_start >= start, meeting_start < end)),
                    Not(And(meeting_end > start, meeting_end <= end)),
                ])
    constraints.extend(margaret_constraints)

    # Define the constraints for Alexis's schedule
    alexis_constraints = []
    for day, schedule in alexis_schedule.items():
        for start, end in schedule:
            if day == 'Monday':
                alexis_constraints.extend([
                    Not(And(alexis_meeting >= start, alexis_meeting < end)),
                    Not(And(meeting_start >= start, meeting_start < end)),
                    Not(And(meeting_end > start, meeting_end <= end)),
                ])
            elif day == 'Tuesday':
                alexis_constraints.extend([
                    Not(And(alexis_meeting >= start, alexis_meeting < 14 * 60 + 30)),
                    Not(And(alexis_meeting >= start, alexis_meeting < end)),
                    Not(And(meeting_start >= start, meeting_start < end)),
                    Not(And(meeting_end > start, meeting_end <= end)),
                ])
    constraints.extend(alexis_constraints)

    # Define the constraint for Margaret avoiding Monday
    margaret_avoid_monday_constraints = [
        Not(And(margaret_meeting >= 0, margaret_meeting < 17 * 60)),
    ]
    constraints.extend(margaret_avoid_monday_constraints)

    # Define the constraint for Margaret avoiding Tuesday before 14:30
    margaret_avoid_tuesday_before_constraints = [
        Not(And(margaret_meeting >= 0, margaret_meeting < 14 * 60 + 30)),
    ]
    constraints.extend(margaret_avoid_tuesday_before_constraints)

    # Define the solver
    solver = Solver()

    # Add the constraints to the solver
    solver.add(constraints)

    # Solve the solver
    result = solver.check()

    # If the solver found a solution, print the meeting time
    if result == sat:
        model = solver.model()
        print(f"Meeting time: {model[margaret_meeting].as_long()} - {model[meeting_end].as_long()}")
    else:
        print("No solution found")

# Example usage
start_time = 9 * 60  # 9:00
end_time = 17 * 60  # 17:00
duration = 30  # 30 minutes
margaret_schedule = {
    'Monday': [(10 * 60 + 30, 11 * 60), (11 * 60 + 30, 12 * 60), (13 * 60, 13 * 60 + 30), (15 * 60, 17 * 60)],
    'Tuesday': [(12 * 60, 12 * 60 + 30)],
}
alexis_schedule = {
    'Monday': [(9 * 60 + 30, 11 * 60 + 30), (12 * 60 + 30, 13 * 60), (14 * 60, 17 * 60)],
    'Tuesday': [(9 * 60, 9 * 60 + 30), (10 * 60, 10 * 60 + 30), (14 * 60, 16 * 60 + 30)],
}
margaret_avoid_monday = True
margaret_avoid_tuesday_before = True

schedule_meeting(start_time, end_time, duration, margaret_schedule, alexis_schedule, margaret_avoid_monday, margaret_avoid_tuesday_before)