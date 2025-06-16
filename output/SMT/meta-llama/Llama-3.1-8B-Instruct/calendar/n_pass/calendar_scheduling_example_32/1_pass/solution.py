from z3 import *

def schedule_meeting(day, start_time, end_time, emily_schedule, melissa_schedule, frank_schedule, frank_preference):
    # Create Z3 variables for the meeting time
    meeting_start = Int('meeting_start')
    meeting_end = Int('meeting_end')

    # Define the constraints for the meeting time
    constraints = [
        And(meeting_start >= 9 * 60, meeting_start < 18 * 60),  # Meeting time must be within work hours
        And(meeting_end > meeting_start, meeting_end < 18 * 60),  # Meeting end time must be after start time and within work hours
        meeting_end - meeting_start == 30  # Meeting duration is 30 minutes
    ]

    # Add constraints for each participant's schedule
    for schedule in [emily_schedule, melissa_schedule, frank_schedule]:
        for start, end in schedule:
            constraints.append(Or(
                And(meeting_start >= start * 60, meeting_start < end * 60),
                And(meeting_end > start * 60, meeting_end < end * 60)
            ))

    # Add constraint for Frank's preference
    if frank_preference:
        constraints.append(meeting_start < 9.5 * 60)

    # Solve the constraints
    solver = Solver()
    solver.add(constraints)
    if solver.check() == sat:
        model = solver.model()
        return f"SOLUTION:\nDay: {day}\nStart Time: {model[meeting_start].as_long() // 60:02d}:{model[meeting_start].as_long() % 60:02d}\nEnd Time: {model[meeting_end].as_long() // 60:02d}:{model[meeting_end].as_long() % 60:02d}"
    else:
        return "No solution found"

# Define the schedules and preferences
emily_schedule = [(10, 10.5), (11.5, 12.5), (14, 15), (16, 16.5)]
melissa_schedule = [(9.5, 10), (14.5, 15)]
frank_schedule = [(10, 10.5), (11, 11.5), (12.5, 13), (13.5, 14.5), (15, 16), (16.5, 17)]
frank_preference = True

# Call the function to schedule the meeting
print(schedule_meeting('Monday', 9, 17, emily_schedule, melissa_schedule, frank_schedule, frank_preference))