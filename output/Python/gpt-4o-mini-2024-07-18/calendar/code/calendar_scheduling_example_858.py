from datetime import datetime, timedelta

# Define working hours and meeting duration
working_hours = (9, 17)
meeting_duration = timedelta(hours=1)

# Define schedules
carl_schedule = {
    "Monday": [(11, 30)],
    "Tuesday": [(14, 30)],
    "Wednesday": [(10, 30), (13, 30)],
    "Thursday": [(13, 30), (16, 30)],
}

margaret_schedule = {
    "Monday": [(9, 30), (11, 0), (17, 0)],
    "Tuesday": [(9, 30), (12, 0), (13, 30), (15, 30)],
    "Wednesday": [(9, 30), (12, 0), (12, 30), (14, 30), (15, 0)],
    "Thursday": [(10, 0), (12, 0), (12, 30), (14, 30)],
}

# Function to check if time is free
def is_free(start_time, end_time, schedule):
    for busy_time in schedule:
        busy_start = timedelta(hours=busy_time[0], minutes=busy_time[1])
        busy_end = busy_start + meeting_duration
        if not (end_time <= busy_start or start_time >= busy_end):
            return False
    return True

# Generate possible meeting times
possible_times = []

for day in ["Monday", "Tuesday", "Wednesday", "Thursday"]:
    # Check time slots within working hours
    for hour in range(working_hours[0], working_hours[1]):
        # Define start and end time
        start_time = timedelta(hours=hour)
        end_time = start_time + meeting_duration
        
        # Check if the time slot is free for both participants
        if is_free(start_time, end_time, carl_schedule.get(day, [])) and \
           is_free(start_time, end_time, margaret_schedule.get(day, [])):
            possible_times.append((day, start_time))

# Filter out Thursday's options if needed
final_times = [(day, time) for day, time in possible_times if day != "Thursday"]

# Select the first suitable time
if final_times:
    day, time = final_times[0]
    proposed_time = (f"{time.seconds // 3600:02}:{(time.seconds // 60) % 60:02}", 
                     f"{(time + meeting_duration).seconds // 3600:02}:{((time + meeting_duration).seconds // 60) % 60:02}")
    print(f"{day}: {proposed_time[0]}:{proposed_time[1]}")