from z3 import *

def schedule_meeting(day, start_time, end_time, emily_schedule, melissa_schedule, frank_schedule, frank_preference):
    # Create Z3 variables for the meeting time
    meeting_start = Int('meeting_start')
    meeting_end = Int('meeting_end')

    # Define the constraints for the meeting time
    constraints = [
        And(meeting_start >= 9 * 60, meeting_start < 18 * 60),  # Meeting time must be within work hours
        meeting_end - meeting_start == 30  # Meeting duration is 30 minutes
    ]

    # Add constraints for each participant's schedule
    emily_available = []
    melissa_available = []
    frank_available = []
    for start, end in emily_schedule:
        emily_available.extend([(start * 60 + i, end * 60 + i) for i in range(60)])
    for start, end in melissa_schedule:
        melissa_available.extend([(start * 60 + i, end * 60 + i) for i in range(60)])
    for start, end in frank_schedule:
        frank_available.extend([(start * 60 + i, end * 60 + i) for i in range(60)])

    # Add constraints for each participant's schedule
    for start, end in emily_available:
        constraints.append(Or(
            And(meeting_start >= start, meeting_start < end),
            And(meeting_end > start, meeting_end < end)
        ))
    for start, end in melissa_available:
        constraints.append(Or(
            And(meeting_start >= start, meeting_start < end),
            And(meeting_end > start, meeting_end < end)
        ))
    for start, end in frank_available:
        constraints.append(Or(
            And(meeting_start >= start, meeting_start < end),
            And(meeting_end > start, meeting_end < end)
        ))

    # Add constraint for Frank's preference
    if frank_preference:
        constraints.append(meeting_start < 9.5 * 60)

    # Add constraint to ensure that the meeting start time is after the last unavailable time slot
    last_unavailable_time = 9 * 60
    for start, end in emily_available + melissa_available + frank_available:
        if end > last_unavailable_time:
            last_unavailable_time = end
    constraints.append(meeting_start >= last_unavailable_time)

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