from z3 import *

def schedule_meeting(start_time, end_time, duration, mary_schedule, alexis_schedule):
    # Create Z3 variables for the meeting time
    mary_meeting = Int('mary_meeting')
    alexis_meeting = Int('alexis_meeting')

    # Create Z3 variables for the start and end times of the meeting
    meeting_start = Int('meeting_start')
    meeting_end = Int('meeting_end')

    # Define the constraints for the meeting time
    constraints = [
        And(mary_meeting >= start_time, mary_meeting <= end_time),
        And(alexis_meeting >= start_time, alexis_meeting <= end_time),
        meeting_start == mary_meeting,
        meeting_end == mary_meeting + duration,
        meeting_start == alexis_meeting,
        meeting_end == alexis_meeting + duration,
    ]

    # Define the constraints for Mary's schedule
    mary_constraints = []
    for day, schedule in mary_schedule.items():
        for start, end in schedule:
            if day == 'Monday':
                mary_constraints.extend([
                    Not(And(mary_meeting >= start, mary_meeting < end)),
                    Not(And(meeting_start >= start, meeting_start < end)),
                    Not(And(meeting_end > start, meeting_end <= end)),
                ])
            elif day == 'Tuesday':
                mary_constraints.extend([
                    Not(And(mary_meeting >= start, mary_meeting < end)),
                    Not(And(meeting_start >= start, meeting_start < end)),
                    Not(And(meeting_end > start, meeting_end <= end)),
                ])
            elif day == 'Wednesday':
                mary_constraints.extend([
                    Not(And(mary_meeting >= start, mary_meeting < end)),
                    Not(And(meeting_start >= start, meeting_start < end)),
                    Not(And(meeting_end > start, meeting_end <= end)),
                ])
            elif day == 'Thursday':
                mary_constraints.extend([
                    Not(And(mary_meeting >= start, mary_meeting < end)),
                    Not(And(meeting_start >= start, meeting_start < end)),
                    Not(And(meeting_end > start, meeting_end <= end)),
                ])
    constraints.extend(mary_constraints)

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
                    Not(And(alexis_meeting >= start, alexis_meeting < end)),
                    Not(And(meeting_start >= start, meeting_start < end)),
                    Not(And(meeting_end > start, meeting_end <= end)),
                ])
            elif day == 'Wednesday':
                alexis_constraints.extend([
                    Not(And(alexis_meeting >= start, alexis_meeting < end)),
                    Not(And(meeting_start >= start, meeting_start < end)),
                    Not(And(meeting_end > start, meeting_end <= end)),
                ])
            elif day == 'Thursday':
                alexis_constraints.extend([
                    Not(And(alexis_meeting >= start, alexis_meeting < end)),
                    Not(And(meeting_start >= start, meeting_start < end)),
                    Not(And(meeting_end > start, meeting_end <= end)),
                ])
    constraints.extend(alexis_constraints)

    # Define the solver
    solver = Solver()

    # Add the constraints to the solver
    solver.add(constraints)

    # Solve the solver
    result = solver.check()

    # If the solver found a solution, print the meeting time
    if result == sat:
        model = solver.model()
        print(f"Meeting time: {model[mary_meeting].as_long()} - {model[meeting_end].as_long()}")
    else:
        print("No solution found")

# Example usage
start_time = 9 * 60  # 9:00
end_time = 17 * 60  # 17:00
duration = 30  # 30 minutes
mary_schedule = {
    'Tuesday': [(10 * 60, 10 * 60 + 30), (15 * 60 + 30, 16 * 60)],
    'Wednesday': [(9 * 60 + 30, 10 * 60), (15 * 60, 15 * 60 + 30)],
    'Thursday': [(9 * 60, 10 * 60), (10 * 60 + 30, 11 * 60 + 30)],
}
alexis_schedule = {
    'Monday': [(9 * 60, 10 * 60), (10 * 60 + 30, 12 * 60), (12 * 60 + 30, 16 * 60 + 30)],
    'Tuesday': [(9 * 60, 10 * 60), (10 * 60 + 30, 11 * 60 + 30), (12 * 60, 15 * 60 + 30), (16 * 60, 17 * 60)],
    'Wednesday': [(9 * 60, 11 * 60), (11 * 60 + 30, 17 * 60)],
    'Thursday': [(10 * 60, 12 * 60), (14 * 60, 14 * 60 + 30), (15 * 60 + 30, 16 * 60), (16 * 60 + 30, 17 * 60)],
}

schedule_meeting(start_time, end_time, duration, mary_schedule, alexis_schedule)