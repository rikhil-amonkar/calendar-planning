from datetime import datetime, timedelta

# Define the meeting duration in minutes
meeting_duration = timedelta(minutes=30)

# Define work hours
work_start = datetime.strptime("09:00", "%H:%M")
work_end = datetime.strptime("17:00", "%H:%M")

# Define busy schedules for each participant (times are relative to work start)
# Times are stored as tuples (start, end) where start and end are datetime objects (time only)
# Note: For simplicity, we use the same reference date.
def get_time(time_str):
    return datetime.strptime(time_str, "%H:%M")

participants_busy = {
    "Julie": {
        # Julie has no meetings the whole week.
        "Monday": [],
        "Tuesday": [],
        "Wednesday": [],
        "Thursday": []
    },
    "Ruth": {
        "Monday": [(get_time("09:00"), get_time("17:00"))],
        "Tuesday": [(get_time("09:00"), get_time("17:00"))],
        "Wednesday": [(get_time("09:00"), get_time("17:00"))],
        "Thursday": [
            (get_time("09:00"), get_time("11:00")),
            (get_time("11:30"), get_time("14:30")),
            (get_time("15:00"), get_time("17:00"))
        ]
    }
}

# Julie's preference: avoid meetings on Thursday before 11:30.
julie_prefer_after = {
    "Thursday": get_time("11:30")
}

# List the candidate days in order
candidate_days = ["Monday", "Tuesday", "Wednesday", "Thursday"]

def is_slot_free(day, start, end):
    """Check if the slot [start, end) is free for all participants."""
    for person, schedule in participants_busy.items():
        for busy_start, busy_end in schedule[day]:
            # if the meeting slot overlaps with a busy slot, return False
            if start < busy_end and busy_start < end:
                return False
    # Additional check for Julie's preference
    if day in julie_prefer_after:
        pref_start = julie_prefer_after[day]
        if start < pref_start:
            return False
    return True

scheduled_day = None
scheduled_start = None
scheduled_end = None

# Try to find a meeting slot on a candidate day
for day in candidate_days:
    # iterate through possible start times (every minute) within working hours
    current_time = get_time("09:00")
    while current_time + meeting_duration <= get_time("17:00"):
        slot_end = current_time + meeting_duration
        if is_slot_free(day, current_time, slot_end):
            scheduled_day = day
            scheduled_start = current_time
            scheduled_end = slot_end
            break
        # move to next minute
        current_time += timedelta(minutes=1)
    if scheduled_day is not None:
        break

# Format the meeting time result as HH:MM:HH:MM and print day.
if scheduled_day is not None:
    time_range = scheduled_start.strftime("%H:%M") + ":" + scheduled_end.strftime("%H:%M")
    print(f"Day: {scheduled_day}, Time: {time_range}")
else:
    print("No available meeting slot found.")