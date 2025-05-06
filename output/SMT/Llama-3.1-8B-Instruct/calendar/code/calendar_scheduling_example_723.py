from z3 import *

def schedule_meeting(start_time, end_time, duration, arthur_schedule, michael_schedule, arthur_avoid_tuesday):
    # Create Z3 variables for the meeting time
    arthur_meeting = Int('arthur_meeting')
    michael_meeting = Int('michael_meeting')

    # Create Z3 variables for the start and end times of the meeting
    meeting_start = Int('meeting_start')
    meeting_end = Int('meeting_end')

    # Define the constraints for the meeting time
    constraints = [
        And(arthur_meeting >= start_time, arthur_meeting <= end_time),
        And(michael_meeting >= start_time, michael_meeting <= end_time),
        meeting_start == arthur_meeting,
        meeting_end == arthur_meeting + duration,
        meeting_start == michael_meeting,
        meeting_end == michael_meeting + duration,
    ]

    # Define the constraints for Arthur's schedule
    arthur_constraints = []
    for day, schedule in arthur_schedule.items():
        for start, end in schedule:
            if day == 'Monday':
                arthur_constraints.extend([
                    Not(And(arthur_meeting >= start, arthur_meeting < end)),
                    Not(And(meeting_start >= start, meeting_start < end)),
                    Not(And(meeting_end > start, meeting_end <= end)),
                ])
            elif day == 'Tuesday':
                arthur_constraints.extend([
                    Not(And(arthur_meeting >= start, arthur_meeting < end)),
                    Not(And(meeting_start >= start, meeting_start < end)),
                    Not(And(meeting_end > start, meeting_end <= end)),
                ])
            elif day == 'Wednesday':
                arthur_constraints.extend([
                    Not(And(arthur_meeting >= start, arthur_meeting < end)),
                    Not(And(meeting_start >= start, meeting_start < end)),
                    Not(And(meeting_end > start, meeting_end <= end)),
                ])
    constraints.extend(arthur_constraints)

    # Define the constraints for Michael's schedule
    michael_constraints = []
    for day, schedule in michael_schedule.items():
        for start, end in schedule:
            if day == 'Monday':
                michael_constraints.extend([
                    Not(And(michael_meeting >= start, michael_meeting < end)),
                    Not(And(meeting_start >= start, meeting_start < end)),
                    Not(And(meeting_end > start, meeting_end <= end)),
                ])
            elif day == 'Tuesday':
                michael_constraints.extend([
                    Not(And(michael_meeting >= start, michael_meeting < end)),
                    Not(And(meeting_start >= start, meeting_start < end)),
                    Not(And(meeting_end > start, meeting_end <= end)),
                ])
            elif day == 'Wednesday':
                michael_constraints.extend([
                    Not(And(michael_meeting >= start, michael_meeting < end)),
                    Not(And(meeting_start >= start, meeting_start < end)),
                    Not(And(meeting_end > start, meeting_end <= end)),
                ])
    constraints.extend(michael_constraints)

    # Define the constraint for Arthur not meeting on Tuesday
    arthur_avoid_tuesday_constraints = [
        Not(And(arthur_meeting >= 0, arthur_meeting < 17 * 60)),
    ]
    constraints.extend(arthur_avoid_tuesday_constraints)

    # Define the solver
    solver = Solver()

    # Add the constraints to the solver
    solver.add(constraints)

    # Solve the solver
    result = solver.check()

    # If the solver found a solution, print the meeting time
    if result == sat:
        model = solver.model()
        print(f"Meeting time: {model[arthur_meeting].as_long()} - {model[meeting_end].as_long()}")
    else:
        print("No solution found")

# Example usage
start_time = 9 * 60  # 9:00
end_time = 17 * 60  # 17:00
duration = 30  # 30 minutes
arthur_schedule = {
    'Monday': [(11 * 60, 11 * 60 + 30), (13 * 60 + 30, 14 * 60), (15 * 60, 15 * 60 + 30)],
    'Tuesday': [(13 * 60, 13 * 60 + 30), (16 * 60, 16 * 60 + 30)],
    'Wednesday': [(10 * 60, 10 * 60 + 30), (11 * 60, 11 * 60 + 30), (12 * 60, 12 * 60 + 30), (14 * 60, 14 * 60 + 30), (16 * 60, 16 * 60 + 30)],
}
michael_schedule = {
    'Monday': [(9 * 60, 12 * 60), (12 * 60 + 30, 13 * 60), (14 * 60, 14 * 60 + 30), (15 * 60, 17 * 60)],
    'Tuesday': [(9 * 60 + 30, 11 * 60 + 30), (12 * 60, 13 * 60 + 30), (14 * 60, 15 * 60 + 30)],
    'Wednesday': [(10 * 60, 12 * 60 + 30), (13 * 60, 13 * 60 + 30)],
}
arthur_avoid_tuesday = True

schedule_meeting(start_time, end_time, duration, arthur_schedule, michael_schedule, arthur_avoid_tuesday)