from datetime import time, timedelta, datetime

# Helper function to convert "HH:MM" string to minutes from midnight
def time_to_minutes(t):
    h, m = map(int, t.split(':'))
    return h * 60 + m

# Helper function to convert minutes from midnight to "HH:MM" string
def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02}:{m:02}"

# Define work hours boundaries in minutes
work_start = time_to_minutes("09:00")
work_end   = time_to_minutes("17:00")
meeting_duration = 60  # minutes

# Define schedules in minutes for Monday and Tuesday for each participant
# Each schedule is a list of (start, end) busy intervals in minutes
schedules = {
    "Monday": {
        "Russell": [(time_to_minutes("10:30"), time_to_minutes("11:00"))],
        "Alexander": [
            (time_to_minutes("09:00"), time_to_minutes("11:30")),
            (time_to_minutes("12:00"), time_to_minutes("14:30")),
            (time_to_minutes("15:00"), time_to_minutes("17:00"))
        ]
    },
    "Tuesday": {
        "Russell": [(time_to_minutes("13:00"), time_to_minutes("13:30"))],
        "Alexander": [
            (time_to_minutes("09:00"), time_to_minutes("10:00")),
            (time_to_minutes("13:00"), time_to_minutes("14:00")),
            (time_to_minutes("15:00"), time_to_minutes("15:30")),
            (time_to_minutes("16:00"), time_to_minutes("16:30"))
        ]
    }
}

# Russell's meeting time preference:
# He would rather not meet on Tuesday before 13:30.
def meets_preferences(day, start):
    if day == "Tuesday" and start < time_to_minutes("13:30"):
        return False
    return True

# Check if a given time slot [slot_start, slot_start + meeting_duration] is free for participant on the given day.
def slot_is_free(busy_slots, slot_start, slot_end):
    for busy_start, busy_end in busy_slots:
        # if meeting overlaps with any busy slot, return False
        if not (slot_end <= busy_start or slot_start >= busy_end):
            return False
    return True

# Try finding a meeting slot for each day in the order Monday then Tuesday.
def find_meeting_slot():
    for day in ["Monday", "Tuesday"]:
        # The potential meeting can only start between work_start and work_end - meeting_duration.
        for start in range(work_start, work_end - meeting_duration + 1):
            end = start + meeting_duration
            
            # Check if this time slot respects Russell's preference
            if not meets_preferences(day, start):
                continue
            
            # Check for all participants if the slot [start, end] is free.
            slot_ok = True
            for participant in schedules[day]:
                if not slot_is_free(schedules[day][participant], start, end):
                    slot_ok = False
                    break
            
            if slot_ok:
                return day, start, end
    return None, None, None

day, start, end = find_meeting_slot()

if day:
    meeting_time_range = f"{minutes_to_time(start)}:{minutes_to_time(end)}"
    print(f"{day} {meeting_time_range}")
else:
    print("No available slot found")