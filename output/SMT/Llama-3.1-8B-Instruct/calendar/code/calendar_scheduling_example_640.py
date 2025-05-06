from z3 import *

def schedule_meeting(start_time, end_time, duration, bobby_schedule, michael_schedule):
    # Create Z3 variables for the meeting time
    bobby_meeting = Int('bobby_meeting')
    michael_meeting = Int('michael_meeting')

    # Create Z3 variables for the start and end times of the meeting
    meeting_start = Int('meeting_start')
    meeting_end = Int('meeting_end')

    # Define the constraints for the meeting time
    constraints = [
        And(bobby_meeting >= start_time, bobby_meeting <= end_time),
        And(michael_meeting >= start_time, michael_meeting <= end_time),
        meeting_start == bobby_meeting,
        meeting_end == bobby_meeting + duration,
        meeting_start == michael_meeting,
        meeting_end == michael_meeting + duration,
    ]

    # Define the constraints for Bobby's schedule
    bobby_constraints = []
    for day, schedule in bobby_schedule.items():
        for start, end in schedule:
            if day == 'Monday':
                bobby_constraints.extend([
                    Not(And(bobby_meeting >= start, bobby_meeting < end)),
                    Not(And(meeting_start >= start, meeting_start < end)),
                    Not(And(meeting_end > start, meeting_end <= end)),
                ])
            elif day == 'Tuesday':
                bobby_constraints.extend([
                    Not(And(bobby_meeting >= start, bobby_meeting < end)),
                    Not(And(meeting_start >= start, meeting_start < end)),
                    Not(And(meeting_end > start, meeting_end <= end)),
                ])
    constraints.extend(bobby_constraints)

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
    constraints.extend(michael_constraints)

    # Define the solver
    solver = Solver()

    # Add the constraints to the solver
    solver.add(constraints)

    # Solve the solver
    result = solver.check()

    # If the solver found a solution, print the meeting time
    if result == sat:
        model = solver.model()
        print(f"Meeting time: {model[bobby_meeting].as_long()} - {model[meeting_end].as_long()}")
    else:
        print("No solution found")

# Example usage
start_time = 9 * 60  # 9:00
end_time = 17 * 60  # 17:00
duration = 30  # 30 minutes
bobby_schedule = {
    'Monday': [(14 * 30, 15 * 0)],
    'Tuesday': [(9 * 0, 11 * 30), (12 * 0, 12 * 30), (13 * 0, 15 * 0), (15 * 30, 17 * 0)],
}
michael_schedule = {
    'Monday': [(9 * 0, 10 * 0), (10 * 30, 13 * 30), (14 * 0, 15 * 0), (15 * 30, 17 * 0)],
    'Tuesday': [(9 * 0, 10 * 30), (11 * 0, 11 * 30), (12 * 0, 14 * 0), (15 * 0, 16 * 0), (16 * 30, 17 * 0)],
}

schedule_meeting(start_time, end_time, duration, bobby_schedule, michael_schedule)