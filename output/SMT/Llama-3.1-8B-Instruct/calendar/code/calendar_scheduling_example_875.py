from z3 import *

def schedule_meeting(start_time, end_time, duration, natalie_schedule, william_schedule):
    # Create Z3 variables for the meeting time
    natalie_meeting = Int('natalie_meeting')
    william_meeting = Int('william_meeting')

    # Create Z3 variables for the start and end times of the meeting
    meeting_start = Int('meeting_start')
    meeting_end = Int('meeting_end')

    # Define the constraints for the meeting time
    constraints = [
        And(natalie_meeting >= start_time, natalie_meeting <= end_time),
        And(william_meeting >= start_time, william_meeting <= end_time),
        meeting_start == natalie_meeting,
        meeting_end == natalie_meeting + duration,
        meeting_start == william_meeting,
        meeting_end == william_meeting + duration,
    ]

    # Define the constraints for Natalie's schedule
    natalie_constraints = []
    for day, schedule in natalie_schedule.items():
        for start, end in schedule:
            if day == 'Monday':
                natalie_constraints.extend([
                    Not(And(natalie_meeting >= start, natalie_meeting < end)),
                    Not(And(meeting_start >= start, meeting_start < end)),
                    Not(And(meeting_end > start, meeting_end <= end)),
                ])
            elif day == 'Tuesday':
                natalie_constraints.extend([
                    Not(And(natalie_meeting >= start, natalie_meeting < end)),
                    Not(And(meeting_start >= start, meeting_start < end)),
                    Not(And(meeting_end > start, meeting_end <= end)),
                ])
            elif day == 'Wednesday':
                natalie_constraints.extend([
                    Not(And(natalie_meeting >= start, natalie_meeting < end)),
                    Not(And(meeting_start >= start, meeting_start < end)),
                    Not(And(meeting_end > start, meeting_end <= end)),
                ])
            elif day == 'Thursday':
                natalie_constraints.extend([
                    Not(And(natalie_meeting >= start, natalie_meeting < end)),
                    Not(And(meeting_start >= start, meeting_start < end)),
                    Not(And(meeting_end > start, meeting_end <= end)),
                ])
    constraints.extend(natalie_constraints)

    # Define the constraints for William's schedule
    william_constraints = []
    for day, schedule in william_schedule.items():
        for start, end in schedule:
            if day == 'Monday':
                william_constraints.extend([
                    Not(And(william_meeting >= start, william_meeting < end)),
                    Not(And(meeting_start >= start, meeting_start < end)),
                    Not(And(meeting_end > start, meeting_end <= end)),
                ])
            elif day == 'Tuesday':
                william_constraints.extend([
                    Not(And(william_meeting >= start, william_meeting < end)),
                    Not(And(meeting_start >= start, meeting_start < end)),
                    Not(And(meeting_end > start, meeting_end <= end)),
                ])
            elif day == 'Wednesday':
                william_constraints.extend([
                    Not(And(william_meeting >= start, william_meeting < end)),
                    Not(And(meeting_start >= start, meeting_start < end)),
                    Not(And(meeting_end > start, meeting_end <= end)),
                ])
            elif day == 'Thursday':
                william_constraints.extend([
                    Not(And(william_meeting >= start, william_meeting < end)),
                    Not(And(meeting_start >= start, meeting_start < end)),
                    Not(And(meeting_end > start, meeting_end <= end)),
                ])
    constraints.extend(william_constraints)

    # Define the solver
    solver = Solver()

    # Add the constraints to the solver
    solver.add(constraints)

    # Solve the solver
    result = solver.check()

    # If the solver found a solution, print the meeting time
    if result == sat:
        model = solver.model()
        print(f"Meeting time: {model[natalie_meeting].as_long()} - {model[meeting_end].as_long()}")
    else:
        print("No solution found")

# Example usage
start_time = 9 * 60  # 9:00
end_time = 17 * 60  # 17:00
duration = 60  # 1 hour
natalie_schedule = {
    'Monday': [(9 * 0, 9 * 30), (10 * 0, 12 * 0), (12 * 30, 13 * 0), (14 * 0, 14 * 30), (15 * 0, 16 * 30)],
    'Tuesday': [(9 * 0, 9 * 30), (10 * 0, 10 * 30), (12 * 30, 14 * 0), (16 * 0, 17 * 0)],
    'Wednesday': [(11 * 0, 11 * 30), (16 * 0, 16 * 30)],
    'Thursday': [(10 * 0, 11 * 0), (11 * 30, 15 * 0), (15 * 30, 16 * 0), (16 * 30, 17 * 0)],
}
william_schedule = {
    'Monday': [(9 * 30, 11 * 0), (11 * 30, 17 * 0)],
    'Tuesday': [(9 * 0, 13 * 0), (13 * 30, 16 * 0)],
    'Wednesday': [(9 * 0, 12 * 30), (13 * 0, 14 * 30), (15 * 30, 16 * 0), (16 * 30, 17 * 0)],
    'Thursday': [(9 * 0, 10 * 30), (11 * 0, 11 * 30), (12 * 0, 12 * 30), (13 * 0, 14 * 0), (15 * 0, 17 * 0)],
}

schedule_meeting(start_time, end_time, duration, natalie_schedule, william_schedule)