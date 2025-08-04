from datetime import datetime, timedelta

# Define the work hours and meeting duration
work_start = datetime.strptime("09:00", "%H:%M")
work_end = datetime.strptime("17:00", "%H:%M")
meeting_duration = timedelta(minutes=30)

# Define the blocked times for Ronald and Amber
ronald_blocked_times = {
    "Monday": [(datetime.strptime("10:30", "%H:%M"), datetime.strptime("11:00", "%H:%M")),
               (datetime.strptime("12:00", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
               (datetime.strptime("15:30", "%H:%M"), datetime.strptime("16:00", "%H:%M"))],
    "Tuesday": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("09:30", "%H:%M")),
                (datetime.strptime("12:00", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
                (datetime.strptime("15:30", "%H:%M"), datetime.strptime("16:30", "%H:%M"))],
    "Wednesday": [(datetime.strptime("09:30", "%H:%M"), datetime.strptime("10:30", "%H:%M")),
                  (datetime.strptime("11:00", "%H:%M"), datetime.strptime("12:00", "%H:%M")),
                  (datetime.strptime("12:30", "%H:%M"), datetime.strptime("13:00", "%H:%M")),
                  (datetime.strptime("13:30", "%H:%M"), datetime.strptime("14:00", "%H:%M")),
                  (datetime.strptime("16:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))]
}

amber_blocked_times = {
    "Monday": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("09:30", "%H:%M")),
               (datetime.strptime("10:00", "%H:%M"), datetime.strptime("10:30", "%H:%M")),
               (datetime.strptime("11:30", "%H:%M"), datetime.strptime("12:00", "%H:%M")),
               (datetime.strptime("12:30", "%H:%M"), datetime.strptime("14:00", "%H:%M")),
               (datetime.strptime("14:30", "%H:%M"), datetime.strptime("15:00", "%H:%M")),
               (datetime.strptime("15:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "Tuesday": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("09:30", "%H:%M")),
                (datetime.strptime("10:00", "%H:%M"), datetime.strptime("11:30", "%H:%M")),
                (datetime.strptime("12:00", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
                (datetime.strptime("13:30", "%H:%M"), datetime.strptime("15:30", "%H:%M")),
                (datetime.strptime("16:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "Wednesday": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("09:30", "%H:%M")),
                  (datetime.strptime("10:00", "%H:%M"), datetime.strptime("10:30", "%H:%M")),
                  (datetime.strptime("11:00", "%H:%M"), datetime.strptime("13:30", "%H:%M")),
                  (datetime.strptime("15:00", "%H:%M"), datetime.strptime("15:30", "%H:%M"))]
}

# Function to check if a time slot is available for both participants
def is_time_slot_available(day, start_time):
    end_time = start_time + meeting_duration
    if any(start_time < r_end and end_time > r_start for r_start, r_end in ronald_blocked_times[day]):
        return False
    if any(start_time < a_end and end_time > a_start for a_start, a_end in amber_blocked_times[day]):
        return False
    return True

# Find the earliest available time slot
for day in ["Monday", "Tuesday", "Wednesday"]:
    current_time = work_start
    while current_time + meeting_duration <= work_end:
        if is_time_slot_available(day, current_time):
            start_time_str = current_time.strftime("%H:%M")
            end_time_str = (current_time + meeting_duration).strftime("%H:%M")
            print(f"{start_time_str}:{end_time_str} {day}")
            break
        current_time += timedelta(minutes=15)