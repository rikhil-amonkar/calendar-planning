from z3 import *

def schedule_meeting(judith_schedule, timothy_schedule, meeting_duration, preferences):
    # Create Z3 solver
    s = Solver()

    # Define variables
    days = ['Monday', 'Tuesday', 'Wednesday']
    times = []
    for day in days:
        for hour in range(9, 17):
            for minute in range(0, 60, 30):
                times.append((day, hour, minute))

    meeting_day, meeting_start_hour, meeting_start_minute = Ints('meeting_day start_hour start_minute')

    # Add constraints
    s.add(meeting_day >= 0)
    s.add(meeting_day < len(days))
    s.add(meeting_start_hour >= 9)
    s.add(meeting_start_hour < 17)
    s.add(meeting_start_minute >= 0)
    s.add(meeting_start_minute < 60)

    # Add constraints based on preferences
    if 'Monday' in preferences['avoid']:
        s.add(meeting_day!= 0)
    if 'Wednesday before 12:00' in preferences['avoid']:
        s.add(meeting_day == 2)
        s.add(meeting_start_hour < 12)

    # Add constraints based on schedules
    for day in range(len(days)):
        for hour in range(9, 17):
            for minute in range(0, 60, 30):
                if (day, hour, minute) in judith_schedule:
                    s.add(meeting_day!= day or meeting_start_hour!= hour or meeting_start_minute!= minute)
                if (day, hour, minute) in timothy_schedule:
                    s.add(meeting_day!= day or meeting_start_hour!= hour or meeting_start_minute!= minute)

    # Add constraint for meeting duration
    s.add(meeting_start_hour + meeting_duration <= 17)

    # Add constraint for meeting time
    s.add(meeting_start_hour * 60 + meeting_start_minute >= meeting_duration * 60)

    # Solve
    if s.check() == sat:
        model = s.model()
        meeting_day_val = model[meeting_day].as_long()
        meeting_start_hour_val = model[meeting_start_hour].as_long()
        meeting_start_minute_val = model[meeting_start_minute].as_long()
        return f"SOLUTION:\nDay: {days[meeting_day_val]}\nStart Time: {meeting_start_hour_val:02d}:{meeting_start_minute_val:02d}\nEnd Time: {(meeting_start_hour_val + meeting_duration):02d}:00"
    else:
        return "No solution found"

# Existing schedules for everyone during the days
judith_schedule = [
    (0, 12, 0), (2, 11, 30)
]
timothy_schedule = [
    (0, 9, 30), (0, 10, 30), (0, 12, 30, 14, 0), (0, 15, 30, 17, 0),
    (1, 9, 30, 13, 0), (1, 13, 30, 14, 0), (1, 14, 30, 17, 0),
    (2, 9, 0, 9, 30), (2, 10, 30, 11, 0), (2, 13, 30, 14, 30), (2, 15, 0, 15, 30), (2, 16, 0, 16, 30)
]

# Meeting duration
meeting_duration = 1

# Preferences
preferences = {
    'avoid': ['Monday', 'Wednesday before 12:00']
}

print(schedule_meeting(judith_schedule, timothy_schedule, meeting_duration, preferences))