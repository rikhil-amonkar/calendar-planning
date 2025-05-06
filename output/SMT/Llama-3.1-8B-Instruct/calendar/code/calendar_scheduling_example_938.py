from z3 import *

def schedule_meeting(start_time, end_time, duration, eugene_schedule, eric_schedule, eric_avoid_wednesday):
    # Create Z3 variables for the meeting time
    eugene_meeting = Int('eugene_meeting')
    eric_meeting = Int('eric_meeting')

    # Create Z3 variables for the start and end times of the meeting
    meeting_start = Int('meeting_start')
    meeting_end = Int('meeting_end')

    # Define the constraints for the meeting time
    constraints = [
        And(eugene_meeting >= start_time, eugene_meeting <= end_time),
        And(eric_meeting >= start_time, eric_meeting <= end_time),
        meeting_start == eugene_meeting,
        meeting_end == eugene_meeting + duration,
        meeting_start == eric_meeting,
        meeting_end == eric_meeting + duration,
    ]

    # Define the constraints for Eugene's schedule
    eugene_constraints = []
    for day, schedule in eugene_schedule.items():
        for start, end in schedule:
            if day == 'Monday':
                eugene_constraints.extend([
                    Not(And(eugene_meeting >= start, eugene_meeting < end)),
                    Not(And(meeting_start >= start, meeting_start < end)),
                    Not(And(meeting_end > start, meeting_end <= end)),
                ])
            elif day == 'Tuesday':
                eugene_constraints.extend([
                    Not(And(eugene_meeting >= start, eugene_meeting < end)),
                    Not(And(meeting_start >= start, meeting_start < end)),
                    Not(And(meeting_end > start, meeting_end <= end)),
                ])
            elif day == 'Wednesday':
                eugene_constraints.extend([
                    Not(And(eugene_meeting >= start, eugene_meeting < end)),
                    Not(And(meeting_start >= start, meeting_start < end)),
                    Not(And(meeting_end > start, meeting_end <= end)),
                ])
            elif day == 'Thursday':
                eugene_constraints.extend([
                    Not(And(eugene_meeting >= start, eugene_meeting < end)),
                    Not(And(meeting_start >= start, meeting_start < end)),
                    Not(And(meeting_end > start, meeting_end <= end)),
                ])
            elif day == 'Friday':
                eugene_constraints.extend([
                    Not(And(eugene_meeting >= start, eugene_meeting < end)),
                    Not(And(meeting_start >= start, meeting_start < end)),
                    Not(And(meeting_end > start, meeting_end <= end)),
                ])
    constraints.extend(eugene_constraints)

    # Define the constraints for Eric's schedule
    eric_constraints = []
    for day, schedule in eric_schedule.items():
        for start, end in schedule:
            if day == 'Monday':
                eric_constraints.extend([
                    Not(And(eric_meeting >= start, eric_meeting < end)),
                    Not(And(meeting_start >= start, meeting_start < end)),
                    Not(And(meeting_end > start, meeting_end <= end)),
                ])
            elif day == 'Tuesday':
                eric_constraints.extend([
                    Not(And(eric_meeting >= start, eric_meeting < end)),
                    Not(And(meeting_start >= start, meeting_start < end)),
                    Not(And(meeting_end > start, meeting_end <= end)),
                ])
            elif day == 'Wednesday':
                eric_constraints.extend([
                    Not(And(eric_meeting >= 0, eric_meeting < 11 * 60 + 30)),
                    Not(And(eric_meeting >= 12 * 60, eric_meeting < 14 * 60)),
                    Not(And(eric_meeting >= 14 * 60 + 30, eric_meeting < 16 * 60 + 30)),
                    Not(And(eric_meeting >= start, eric_meeting < end)),
                    Not(And(meeting_start >= start, meeting_start < end)),
                    Not(And(meeting_end > start, meeting_end <= end)),
                ])
            elif day == 'Thursday':
                eric_constraints.extend([
                    Not(And(eric_meeting >= start, eric_meeting < end)),
                    Not(And(meeting_start >= start, meeting_start < end)),
                    Not(And(meeting_end > start, meeting_end <= end)),
                ])
            elif day == 'Friday':
                eric_constraints.extend([
                    Not(And(eric_meeting >= start, eric_meeting < end)),
                    Not(And(meeting_start >= start, meeting_start < end)),
                    Not(And(meeting_end > start, meeting_end <= end)),
                ])
    constraints.extend(eric_constraints)

    # Define the constraint for Eric avoiding meetings on Wednesday
    eric_avoid_wednesday_constraints = [
        Not(And(eric_meeting >= 0, eric_meeting < 11 * 60 + 30)),
        Not(And(eric_meeting >= 12 * 60, eric_meeting < 14 * 60)),
        Not(And(eric_meeting >= 14 * 60 + 30, eric_meeting < 16 * 60 + 30)),
    ]
    constraints.extend(eric_avoid_wednesday_constraints)

    # Define the solver
    solver = Solver()

    # Add the constraints to the solver
    solver.add(constraints)

    # Solve the solver
    result = solver.check()

    # If the solver found a solution, print the meeting time
    if result == sat:
        model = solver.model()
        print(f"Meeting time: {model[eugene_meeting].as_long()} - {model[meeting_end].as_long()}")
    else:
        print("No solution found")

# Example usage
start_time = 9 * 60  # 9:00
end_time = 17 * 60  # 17:00
duration = 30  # 30 minutes
eugene_schedule = {
    'Monday': [(11 * 60, 12 * 60), (13 * 60 + 30, 14 * 60), (14 * 60 + 30, 15 * 60), (16 * 60, 16 * 60 + 30)],
    'Wednesday': [(9 * 60, 9 * 60 + 30), (11 * 60, 11 * 60 + 30), (12 * 60, 12 * 60 + 30), (13 * 60 + 30, 15 * 60)],
    'Thursday': [(9 * 60 + 30, 10 * 60), (11 * 60, 12 * 60 + 30)],
    'Friday': [(10 * 60 + 30, 11 * 60), (12 * 60, 12 * 60 + 30), (13 * 60, 13 * 60 + 30)],
}
eric_schedule = {
    'Monday': [(9 * 60, 17 * 60)],
    'Tuesday': [(9 * 60, 17 * 60)],
    'Wednesday': [(9 * 60, 11 * 60 + 30), (12 * 60, 14 * 60), (14 * 60 + 30, 16 * 60 + 30)],
    'Thursday': [(9 * 60, 17 * 60)],
    'Friday': [(9 * 60, 11 * 60), (11 * 60 + 30, 17 * 60)],
}
eric_avoid_wednesday = True

schedule_meeting(start_time, end_time, duration, eugene_schedule, eric_schedule, eric_avoid_wednesday)