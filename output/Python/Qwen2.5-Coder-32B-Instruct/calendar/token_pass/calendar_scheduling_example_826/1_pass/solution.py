# Define the working hours and meeting duration
start_time = 9 * 60  # 9:00 AM in minutes since start of the day
end_time = 17 * 60   # 5:00 PM in minutes since start of the day
meeting_duration = 30  # Meeting duration in minutes

# Define the days of the week and their corresponding indices
days_of_week = ["Monday", "Tuesday", "Wednesday", "Thursday"]

# Define James' busy times in minutes since start of the day
james_busy_times = {
    "Monday": [(9*60, 9*60+30), (10*60+30, 11*60), (12*60+30, 13*60), (14*60+30, 15*60+30), (16*60+30, 17*60)],
    "Tuesday": [(9*60, 11*60), (11*60+30, 12*60), (12*60+30, 15*60+30), (16*60, 17*60)],
    "Wednesday": [(10*60, 11*60), (12*60, 13*60), (13*60+30, 16*60)],
    "Thursday": [(9*60+30, 11*60+30), (12*60, 12*60+30), (13*60, 13*60+30), (14*60, 14*60+30), (16*60+30, 17*60)]
}

# Cheryl does not prefer Wednesday and Thursday
dispreferred_days = {"Wednesday", "Thursday"}

# Function to check if a time slot is free for James
def is_slot_free(day, start, end):
    for busy_start, busy_end in james_busy_times[day]:
        if not (end <= busy_start or start >= busy_end):
            return False
    return True

# Find the earliest available slot
for day in days_of_week:
    if day in dispreferred_days:
        continue  # Skip dispreferred days unless no other option
    current_time = start_time
    while current_time + meeting_duration <= end_time:
        if is_slot_free(day, current_time, current_time + meeting_duration):
            # Convert back to HH:MM format
            start_hour, start_minute = divmod(current_time, 60)
            end_hour, end_minute = divmod(current_time + meeting_duration, 60)
            print(f"{start_hour:02}:{start_minute:02}:{end_hour:02}:{end_minute:02} {day}")
            break
        current_time += 15  # Check every 15 minutes for better granularity
    else:
        continue
    break