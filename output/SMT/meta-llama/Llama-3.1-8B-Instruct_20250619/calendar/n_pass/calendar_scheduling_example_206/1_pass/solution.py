from z3 import *

def schedule_meeting(day, start_time, end_time, schedules, preferences):
    # Create a Z3 solver
    solver = Solver()

    # Define the variables
    meeting_start = Int('meeting_start')
    meeting_end = Int('meeting_end')

    # Add constraints for the meeting duration
    solver.add(And(meeting_start >= start_time, meeting_end <= end_time))
    solver.add(meeting_end - meeting_start == 30)  # 30 minutes meeting duration

    # Add constraints for the schedules
    for person, schedule in schedules.items():
        for time in schedule:
            solver.add(Or(meeting_start + 30 > time[1], meeting_start < time[0]))

    # Add constraints for the preferences
    for person, preference in preferences.items():
        if preference and meeting_start < start_time:
            solver.add(False)  # If the preference is True, the meeting cannot start before the preferred time

    # Check if a solution exists
    if solver.check() == sat:
        model = solver.model()
        meeting_start_value = model[meeting_start].as_long()
        meeting_end_value = model[meeting_end].as_long()
        return f'SOLUTION:\nDay: {day}\nStart Time: {meeting_start_value:02d}:00\nEnd Time: {meeting_end_value:02d}:30'
    else:
        return 'No solution exists'

# Define the schedules and preferences
schedules = {
    'Shirley': [(10*60 + 30, 11*60 + 0), (12*60 + 0, 12*60 + 30)],
    'Jacob': [(9*60 + 0, 9*60 + 30), (10*60 + 0, 10*60 + 30), (11*60 + 0, 11*60 + 30), (12*60 + 30, 13*60 + 30), (14*60 + 30, 15*60 + 0)],
    'Stephen': [(11*60 + 30, 12*60 + 0), (12*60 + 30, 13*60 + 0)],
    'Margaret': [(9*60 + 0, 9*60 + 30), (10*60 + 30, 12*60 + 30), (13*60 + 0, 13*60 + 30), (15*60 + 0, 15*60 + 30), (16*60 + 30, 17*60 + 0)],
    'Mason': [(9*60 + 0, 10*60 + 0), (10*60 + 30, 11*60 + 0), (11*60 + 30, 12*60 + 30), (13*60 + 0, 13*60 + 30), (14*60 + 0, 14*60 + 30), (16*60 + 30, 17*60 + 0)]
}
preferences = {
    'Margaret': True
}

# Find a time that works for everyone's schedule and constraints
day = 'Monday'
start_time = 9*60
end_time = 17*60
print(schedule_meeting(day, start_time, end_time, schedules, preferences))