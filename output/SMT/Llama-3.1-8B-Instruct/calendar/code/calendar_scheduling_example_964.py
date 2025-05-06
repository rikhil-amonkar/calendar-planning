from z3 import *

def schedule_meeting(start_time, end_time, duration, betty_schedule, megan_schedule, betty_cannot_meet_on):
    # Create Z3 variables for the meeting time
    betty_meeting = Int('betty_meeting')
    megan_meeting = Int('megan_meeting')

    # Create Z3 variables for the start and end times of the meeting
    meeting_start = Int('meeting_start')
    meeting_end = Int('meeting_end')

    # Define the constraints for the meeting time
    constraints = [
        And(betty_meeting >= start_time, betty_meeting <= end_time),
        And(megan_meeting >= start_time, megan_meeting <= end_time),
        meeting_start == betty_meeting,
        meeting_end == betty_meeting + duration,
        meeting_start == megan_meeting,
        meeting_end == megan_meeting + duration,
    ]

    # Define the constraints for Betty's schedule
    betty_constraints = []
    for day, schedule in betty_schedule.items():
        for start, end in schedule:
            if day == 'Monday':
                betty_constraints.extend([
                    Not(And(betty_meeting >= start, betty_meeting < end)),
                    Not(And(meeting_start >= start, meeting_start < end)),
                    Not(And(meeting_end > start, meeting_end <= end)),
                ])
            elif day == 'Tuesday':
                betty_constraints.extend([
                    Not(And(betty_meeting >= start, betty_meeting < end)),
                    Not(And(meeting_start >= start, meeting_start < end)),
                    Not(And(meeting_end > start, meeting_end <= end)),
                ])
            elif day == 'Wednesday':
                betty_constraints.extend([
                    Not(And(betty_meeting >= start, betty_meeting < end)),
                    Not(And(meeting_start >= start, meeting_start < end)),
                    Not(And(meeting_end > start, meeting_end <= end)),
                ])
            elif day == 'Thursday':
                betty_constraints.extend([
                    Not(And(betty_meeting >= start, betty_meeting < end)),
                    Not(And(meeting_start >= start, meeting_start < end)),
                    Not(And(meeting_end > start, meeting_end <= end)),
                ])
            elif day == 'Friday':
                betty_constraints.extend([
                    Not(And(betty_meeting >= start, betty_meeting < end)),
                    Not(And(meeting_start >= start, meeting_start < end)),
                    Not(And(meeting_end > start, meeting_end <= end)),
                ])
    constraints.extend(betty_constraints)

    # Define the constraints for Megan's schedule
    megan_constraints = []
    for day, schedule in megan_schedule.items():
        for start, end in schedule:
            if day == 'Monday':
                megan_constraints.extend([
                    Not(And(megan_meeting >= start, megan_meeting < end)),
                    Not(And(meeting_start >= start, meeting_start < end)),
                    Not(And(meeting_end > start, meeting_end <= end)),
                ])
            elif day == 'Tuesday':
                megan_constraints.extend([
                    Not(And(megan_meeting >= start, megan_meeting < 9 * 60 + 30)),
                    Not(And(megan_meeting >= 10 * 60, megan_meeting < 10 * 60 + 30)),
                    Not(And(megan_meeting >= 12 * 60, megan_meeting < 14 * 60)),
                    Not(And(megan_meeting >= 15 * 60, megan_meeting < 15 * 60 + 30)),
                    Not(And(megan_meeting >= 16 * 60, megan_meeting <= 16 * 60 + 30)),
                ])
            elif day == 'Wednesday':
                megan_constraints.extend([
                    Not(And(megan_meeting >= 9 * 60 + 30, megan_meeting < 10 * 60 + 30)),
                    Not(And(megan_meeting >= 11 * 60, megan_meeting < 11 * 60 + 30)),
                    Not(And(megan_meeting >= 12 * 60 + 30, megan_meeting < 13 * 60)),
                    Not(And(megan_meeting >= 13 * 60 + 30, megan_meeting < 14 * 60 + 30)),
                    Not(And(megan_meeting >= 15 * 60 + 30, megan_meeting <= 17 * 60)),
                ])
            elif day == 'Thursday':
                megan_constraints.extend([
                    Not(And(megan_meeting >= 9 * 60, megan_meeting < 10 * 60 + 30)),
                    Not(And(megan_meeting >= 11 * 60 + 30, megan_meeting < 14 * 60)),
                    Not(And(megan_meeting >= 14 * 60 + 30, megan_meeting < 15 * 60)),
                    Not(And(megan_meeting >= 15 * 60 + 30, megan_meeting <= 16 * 60 + 30)),
                ])
            elif day == 'Friday':
                megan_constraints.extend([
                    Not(And(megan_meeting >= 9 * 60, megan_meeting < 17 * 60)),
                ])
    constraints.extend(megan_constraints)

    # Define the constraint for Betty not meeting on Wednesday, Thursday
    betty_cannot_meet_on_constraints = [
        Not(And(betty_meeting >= 0, betty_meeting <= 17 * 60)),
    ]
    constraints.extend(betty_cannot_meet_on_constraints)

    # Define the solver
    solver = Solver()

    # Add the constraints to the solver
    solver.add(constraints)

    # Solve the solver
    result = solver.check()

    # If the solver found a solution, print the meeting time
    if result == sat:
        model = solver.model()
        print(f"Meeting time: {model[betty_meeting].as_long()} - {model[meeting_end].as_long()}")
    else:
        print("No solution found")

# Example usage
start_time = 9 * 60  # 9:00
end_time = 17 * 60  # 17:00
duration = 60  # 1 hour
betty_schedule = {
    'Monday': [(10 * 60, 10 * 60 + 30), (11 * 60 + 30, 12 * 60 + 30), (16 * 60, 16 * 60 + 30)],
    'Tuesday': [(9 * 60 + 30, 10 * 60), (10 * 60 + 30, 11 * 60), (12 * 60, 12 * 60 + 30), (13 * 60 + 30, 15 * 60), (16 * 60 + 30, 17 * 60)],
    'Wednesday': [(13 * 60 + 30, 14 * 60)],
    'Friday': [(9 * 60, 10 * 60), (11 * 60 + 30, 12 * 60), (12 * 60 + 30, 13 * 60), (14 * 60 + 30, 15 * 60)],
}
megan_schedule = {
    'Monday': [(9 * 60, 17 * 60)],
    'Tuesday': [(9 * 60, 9 * 60 + 30), (10 * 60, 10 * 60 + 30), (12 * 60, 14 * 60), (15 * 60, 15 * 60 + 30), (16 * 60, 16 * 60 + 30)],
    'Wednesday': [(9 * 60 + 30, 10 * 60 + 30), (11 * 60, 11 * 60 + 30), (12 * 60 + 30, 13 * 60), (13 * 60 + 30, 14 * 60 + 30), (15 * 60 + 30, 17 * 60)],
    'Thursday': [(9 * 60, 10 * 60 + 30), (11 * 60 + 30, 14 * 60), (14 * 60 + 30, 15 * 60), (15 * 60 + 30, 16 * 60 + 30)],
    'Friday': [(9 * 60, 17 * 60)],
}
betty_cannot_meet_on = [True, True]

schedule_meeting(start_time, end_time, duration, betty_schedule, megan_schedule, betty_cannot_meet_on)