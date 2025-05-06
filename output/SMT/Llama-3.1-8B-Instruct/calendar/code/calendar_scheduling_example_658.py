from z3 import *

def schedule_meeting(start_time, end_time, duration, shirley_schedule, albert_schedule, shirley_avoid_tuesday_after):
    # Create Z3 variables for the meeting time
    shirley_meeting = Int('shirley_meeting')
    albert_meeting = Int('albert_meeting')

    # Create Z3 variables for the start and end times of the meeting
    meeting_start = Int('meeting_start')
    meeting_end = Int('meeting_end')

    # Define the constraints for the meeting time
    constraints = [
        And(shirley_meeting >= start_time, shirley_meeting <= end_time),
        And(albert_meeting >= start_time, albert_meeting <= end_time),
        meeting_start == shirley_meeting,
        meeting_end == shirley_meeting + duration,
        meeting_start == albert_meeting,
        meeting_end == albert_meeting + duration,
    ]

    # Define the constraints for Shirley's schedule
    shirley_constraints = []
    for day, schedule in shirley_schedule.items():
        for start, end in schedule:
            if day == 'Monday':
                shirley_constraints.extend([
                    Not(And(shirley_meeting >= start, shirley_meeting < end)),
                    Not(And(meeting_start >= start, meeting_start < end)),
                    Not(And(meeting_end > start, meeting_end <= end)),
                ])
            elif day == 'Tuesday':
                shirley_constraints.extend([
                    Not(And(shirley_meeting >= start, shirley_meeting < 10 * 60 + 30)),
                    Not(And(shirley_meeting >= start, shirley_meeting < end)),
                    Not(And(meeting_start >= start, meeting_start < end)),
                    Not(And(meeting_end > start, meeting_end <= end)),
                ])
    constraints.extend(shirley_constraints)

    # Define the constraints for Albert's schedule
    albert_constraints = []
    for day, schedule in albert_schedule.items():
        for start, end in schedule:
            if day == 'Monday':
                albert_constraints.extend([
                    Not(And(albert_meeting >= start, albert_meeting < end)),
                    Not(And(meeting_start >= start, meeting_start < end)),
                    Not(And(meeting_end > start, meeting_end <= end)),
                ])
            elif day == 'Tuesday':
                albert_constraints.extend([
                    Not(And(albert_meeting >= start, albert_meeting < end)),
                    Not(And(meeting_start >= start, meeting_start < end)),
                    Not(And(meeting_end > start, meeting_end <= end)),
                ])
    constraints.extend(albert_constraints)

    # Define the constraint for Shirley not meeting on Tuesday after 10:30
    shirley_avoid_tuesday_after_constraints = [
        Not(And(shirley_meeting >= 10 * 60 + 30, shirley_meeting <= 17 * 60)),
    ]
    constraints.extend(shirley_avoid_tuesday_after_constraints)

    # Define the solver
    solver = Solver()

    # Add the constraints to the solver
    solver.add(constraints)

    # Solve the solver
    result = solver.check()

    # If the solver found a solution, print the meeting time
    if result == sat:
        model = solver.model()
        print(f"Meeting time: {model[shirley_meeting].as_long()} - {model[meeting_end].as_long()}")
    else:
        print("No solution found")

# Example usage
start_time = 9 * 60  # 9:00
end_time = 17 * 60  # 17:00
duration = 30  # 30 minutes
shirley_schedule = {
    'Monday': [(10 * 60 + 30, 11 * 60), (12 * 60, 12 * 60 + 30), (16 * 60, 16 * 60 + 30)],
    'Tuesday': [(9 * 60 + 30, 10 * 60)],
}
albert_schedule = {
    'Monday': [(9 * 60, 17 * 60)],
    'Tuesday': [(9 * 60 + 30, 11 * 60), (11 * 60 + 30, 12 * 60 + 30), (13 * 60, 16 * 60), (16 * 60 + 30, 17 * 60)],
}
shirley_avoid_tuesday_after = True

schedule_meeting(start_time, end_time, duration, shirley_schedule, albert_schedule, shirley_avoid_tuesday_after)