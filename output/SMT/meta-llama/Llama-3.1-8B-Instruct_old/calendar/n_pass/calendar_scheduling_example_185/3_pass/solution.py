from z3 import *

def schedule_meeting(day, meeting_duration, schedules, preferences):
    # Create a Z3 solver
    s = Solver()

    # Define the time slots
    start_time = 9 * 60  # 9:00
    end_time = 17 * 60  # 17:00
    time_slots = [i for i in range(start_time, end_time - meeting_duration + 1)]

    # Define the variables
    meeting_start = Int('meeting_start')
    meeting_end = Int('meeting_end')

    # Add constraints
    s.add(meeting_start >= start_time)
    s.add(meeting_end <= end_time)
    s.add(meeting_start + meeting_duration == meeting_end)

    # Add constraints for each participant
    for participant, schedule in schedules.items():
        for time in schedule:
            s.add(meeting_start + meeting_duration > time[0] * 60 + time[1])
            s.add(meeting_start < time[0] * 60 + time[1] + meeting_duration)

    # Add preference constraints
    for participant, preference in preferences.items():
        if preference:
            s.add(meeting_start >= 10 * 60)  # 10:00

    # Check if a solution exists
    if s.check() == sat:
        # Get the solution
        meeting_start_value = s.model()[meeting_start].as_long()
        meeting_end_value = meeting_start_value + meeting_duration

        # Return the solution
        return f"Day: {day}\nStart Time: {meeting_start_value // 60:02d}:{meeting_start_value % 60:02d}\nEnd Time: {meeting_end_value // 60:02d}:{meeting_end_value % 60:02d}"
    else:
        return "No solution exists"

# Define the schedules and preferences
schedules = {
    'Kimberly': [(10, 0), (11, 0), (16, 0)],
    'Megan': [],
    'Marie': [(10, 0), (11, 30), (16, 0)],
    'Diana': [(9, 30), (10, 30), (15, 30)]
}

preferences = {
    'Megan': True
}

# Call the function
print("SOLUTION:")
print(schedule_meeting('Monday', 30, schedules, preferences))