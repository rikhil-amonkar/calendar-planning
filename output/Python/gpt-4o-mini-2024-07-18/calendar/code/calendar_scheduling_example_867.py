from datetime import datetime, timedelta

# Define the schedules
betty_busy_times = {
    "Monday": [(10, 30), (13, 30), (15, 0), (16, 0)],
    "Tuesday": [(9, 0), (11, 30), (12, 30), (13, 30), (16, 30)],
    "Wednesday": [(9, 30), (13, 0), (14, 0)],
    "Thursday": [(9, 30), (11, 30), (14, 0), (15, 0), (16, 30)]
}

scott_busy_times = {
    "Monday": [(9, 30), (15, 0), (16, 0)],
    "Tuesday": [(9, 0), (10, 0), (11, 30), (12, 30), (14, 0), (16, 0)],
    "Wednesday": [(9, 30), (13, 0), (14, 0), (15, 0), (16, 0)],
    "Thursday": [(9, 0), (10, 0), (11, 0), (12, 30), (15, 0), (16, 30)]
}

# Duration of the meeting in minutes
meeting_duration = 30

# Define working days and constraints
working_days = ["Monday", "Tuesday", "Wednesday", "Thursday"]
betty_constraints = {"Monday": False, "Tuesday": "15:00", "Thursday": "15:00"}
scott_constraints = {"Wednesday": "avoid"}

# Function to check for available time slots
def is_time_available(day, start_hour, start_minute):
    end_hour = start_hour + (start_minute + meeting_duration) // 60
    end_minute = (start_minute + meeting_duration) % 60
    if end_hour >= 17:  
        return False
    
    for start, end in betty_busy_times.get(day, []):
        if (start_hour < end) and (start < end_hour or (start == end_hour and start_minute < end_minute)):
            return False
            
    for start, end in scott_busy_times.get(day, []):
        if (start_hour < end) and (start < end_hour or (start == end_hour and start_minute < end_minute)):
            return False
    
    return True

# Find suitable time
proposed_time = None
for day in working_days:
    if not betty_constraints[day]:  # Betty isn't available on Monday
        continue
    for hour in range(9, 17):
        for minute in [0, 30]:
            if is_time_available(day, hour, minute):
                proposed_time = f"{day}, {hour:02}:{minute:02}:{hour:02}:{minute+meeting_duration:02}"
                break
        if proposed_time:
            break
    if proposed_time:
        break

print(proposed_time)