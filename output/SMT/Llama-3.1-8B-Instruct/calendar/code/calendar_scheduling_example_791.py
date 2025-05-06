from z3 import *

def schedule_meeting(start_time, end_time, duration, nicole_schedule, ruth_schedule, ruth_avoid_after):
    # Create Z3 variables for the meeting time
    nicole_meeting = Int('nicole_meeting')
    ruth_meeting = Int('ruth_meeting')

    # Create Z3 variables for the start and end times of the meeting
    meeting_start = Int('meeting_start')
    meeting_end = Int('meeting_end')

    # Define the constraints for the meeting time
    constraints = [
        And(nicole_meeting >= start_time, nicole_meeting <= end_time),
        And(ruth_meeting >= start_time, ruth_meeting <= end_time),
        meeting_start == nicole_meeting,
        meeting_end == nicole_meeting + duration,
        meeting_start == ruth_meeting,
        meeting_end == ruth_meeting + duration,
    ]

    # Define the constraints for Nicole's schedule
    nicole_constraints = []
    for day, schedule in nicole_schedule.items():
        for start, end in schedule:
            if day == 'Monday':
                nicole_constraints.extend([
                    Not(And(nicole_meeting >= start, nicole_meeting < end)),
                    Not(And(meeting_start >= start, meeting_start < end)),
                    Not(And(meeting_end > start, meeting_end <= end)),
                ])
            elif day == 'Tuesday':
                nicole_constraints.extend([
                    Not(And(nicole_meeting >= start, nicole_meeting < end)),
                    Not(And(meeting_start >= start, meeting_start < end)),
                    Not(And(meeting_end > start, meeting_end <= end)),
                ])
            elif day == 'Wednesday':
                nicole_constraints.extend([
                    Not(And(nicole_meeting >= start, nicole_meeting < end)),
                    Not(And(meeting_start >= start, meeting_start < end)),
                    Not(And(meeting_end > start, meeting_end <= end)),
                ])
    constraints.extend(nicole_constraints)

    # Define the constraints for Ruth's schedule
    ruth_constraints = []
    for day, schedule in ruth_schedule.items():
        for start, end in schedule:
            if day == 'Monday':
                ruth_constraints.extend([
                    Not(And(ruth_meeting >= start, ruth_meeting < 17 * 60)),
                ])
            elif day == 'Tuesday':
                ruth_constraints.extend([
                    Not(And(ruth_meeting >= start, ruth_meeting < 17 * 60)),
                ])
            elif day == 'Wednesday':
                ruth_constraints.extend([
                    Not(And(ruth_meeting >= start, ruth_meeting < 13 * 30)),
                ])
    constraints.extend(ruth_constraints)

    # Define the solver
    solver = Solver()

    # Add the constraints to the solver
    solver.add(constraints)

    # Solve the solver
    result = solver.check()

    # If the solver found a solution, print the meeting time
    if result == sat:
        model = solver.model()
        print(f"Meeting time: {model[nicole_meeting].as_long()} - {model[meeting_end].as_long()}")
    else:
        print("No solution found")

# Example usage
start_time = 9 * 60  # 9:00
end_time = 17 * 60  # 17:00
duration = 30  # 30 minutes
nicole_schedule = {
    'Monday': [(9 * 0, 9 * 30), (13 * 0, 13 * 30), (14 * 30, 15 * 30)],
    'Tuesday': [(9 * 0, 9 * 30), (11 * 30, 13 * 30), (14 * 30, 15 * 30)],
    'Wednesday': [(10 * 0, 11 * 0), (12 * 30, 15 * 0), (16 * 0, 17 * 0)],
}
ruth_schedule = {
    'Monday': [(9 * 0, 17 * 60)],
    'Tuesday': [(9 * 0, 17 * 60)],
    'Wednesday': [(9 * 0, 10 * 30), (11 * 0, 11 * 30), (12 * 0, 12 * 30), (13 * 30, 15 * 30), (16 * 0, 16 * 30)],
}
ruth_avoid_after = True

schedule_meeting(start_time, end_time, duration, nicole_schedule, ruth_schedule, ruth_avoid_after)