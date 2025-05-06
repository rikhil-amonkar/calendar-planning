from z3 import *

def schedule_meeting(start_time, end_time, duration, martha_schedule, beverly_schedule):
    # Create Z3 variables for the meeting time
    martha_meeting = Int('martha_meeting')
    beverly_meeting = Int('beverly_meeting')

    # Create Z3 variables for the start and end times of the meeting
    meeting_start = Int('meeting_start')
    meeting_end = Int('meeting_end')

    # Define the constraints for the meeting time
    constraints = [
        And(martha_meeting >= start_time, martha_meeting <= end_time),
        And(beverly_meeting >= start_time, beverly_meeting <= end_time),
        meeting_start == martha_meeting,
        meeting_end == martha_meeting + duration,
        meeting_start == beverly_meeting,
        meeting_end == beverly_meeting + duration,
    ]

    # Define the constraints for Martha's schedule
    martha_constraints = []
    for day, schedule in martha_schedule.items():
        for start, end in schedule:
            if day == 'Monday':
                martha_constraints.extend([
                    Not(And(martha_meeting >= start, martha_meeting < end)),
                    Not(And(meeting_start >= start, meeting_start < end)),
                    Not(And(meeting_end > start, meeting_end <= end)),
                ])
            elif day == 'Tuesday':
                martha_constraints.extend([
                    Not(And(martha_meeting >= start, martha_meeting < end)),
                    Not(And(meeting_start >= start, meeting_start < end)),
                    Not(And(meeting_end > start, meeting_end <= end)),
                ])
            elif day == 'Wednesday':
                martha_constraints.extend([
                    Not(And(martha_meeting >= start, martha_meeting < end)),
                    Not(And(meeting_start >= start, meeting_start < end)),
                    Not(And(meeting_end > start, meeting_end <= end)),
                ])
    constraints.extend(martha_constraints)

    # Define the constraints for Beverly's schedule
    beverly_constraints = []
    for day, schedule in beverly_schedule.items():
        for start, end in schedule:
            if day == 'Monday':
                beverly_constraints.extend([
                    Not(And(beverly_meeting >= start, beverly_meeting < 13 * 30)),
                    Not(And(beverly_meeting >= start, beverly_meeting < end)),
                    Not(And(meeting_start >= start, meeting_start < end)),
                    Not(And(meeting_end > start, meeting_end <= end)),
                ])
            elif day == 'Tuesday':
                beverly_constraints.extend([
                    Not(And(beverly_meeting >= start, beverly_meeting < end)),
                    Not(And(meeting_start >= start, meeting_start < end)),
                    Not(And(meeting_end > start, meeting_end <= end)),
                ])
            elif day == 'Wednesday':
                beverly_constraints.extend([
                    Not(And(beverly_meeting >= start, beverly_meeting < end)),
                    Not(And(meeting_start >= start, meeting_start < end)),
                    Not(And(meeting_end > start, meeting_end <= end)),
                ])
    constraints.extend(beverly_constraints)

    # Define the solver
    solver = Solver()

    # Add the constraints to the solver
    solver.add(constraints)

    # Solve the solver
    result = solver.check()

    # If the solver found a solution, print the meeting time
    if result == sat:
        model = solver.model()
        print(f"Meeting time: {model[martha_meeting].as_long()} - {model[meeting_end].as_long()}")
    else:
        print("No solution found")

# Example usage
start_time = 9 * 60  # 9:00
end_time = 17 * 60  # 17:00
duration = 60  # 1 hour
martha_schedule = {
    'Monday': [(16 * 0, 17 * 0)],
    'Tuesday': [(15 * 0, 15 * 30)],
    'Wednesday': [(10 * 0, 11 * 0), (14 * 0, 14 * 30)],
}
beverly_schedule = {
    'Monday': [(9 * 0, 13 * 30), (14 * 0, 17 * 0)],
    'Tuesday': [(9 * 0, 17 * 0)],
    'Wednesday': [(9 * 30, 15 * 30), (16 * 30, 17 * 0)],
}

schedule_meeting(start_time, end_time, duration, martha_schedule, beverly_schedule)