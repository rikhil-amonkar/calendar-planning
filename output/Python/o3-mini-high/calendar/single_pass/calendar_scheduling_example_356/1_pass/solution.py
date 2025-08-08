from datetime import datetime, timedelta

# Define helper functions for time conversion
def time_to_minutes(time_str):
    # time_str in "HH:MM" format
    h, m = map(int, time_str.split(":"))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

# Meeting parameters
meeting_duration = 30  # in minutes
day = "Monday"
work_start = time_to_minutes("09:00")
work_end = time_to_minutes("17:00")

# Busy intervals for each participant (each interval is a tuple (start, end) in minutes)
busy = {
    "Katherine": [(time_to_minutes("12:00"), time_to_minutes("12:30")),
                  (time_to_minutes("13:00"), time_to_minutes("14:30"))],
    "Rebecca": [],  # No meetings
    "Julie": [(time_to_minutes("09:00"), time_to_minutes("09:30")),
              (time_to_minutes("10:30"), time_to_minutes("11:00")),
              (time_to_minutes("13:30"), time_to_minutes("14:00")),
              (time_to_minutes("15:00"), time_to_minutes("15:30"))],
    "Angela": [(time_to_minutes("09:00"), time_to_minutes("10:00")),
               (time_to_minutes("10:30"), time_to_minutes("11:00")),
               (time_to_minutes("11:30"), time_to_minutes("14:00")),
               (time_to_minutes("14:30"), time_to_minutes("15:00")),
               (time_to_minutes("16:30"), time_to_minutes("17:00"))],
    "Nicholas": [(time_to_minutes("09:30"), time_to_minutes("11:00")),
                 (time_to_minutes("11:30"), time_to_minutes("13:30")),
                 (time_to_minutes("14:00"), time_to_minutes("16:00")),
                 (time_to_minutes("16:30"), time_to_minutes("17:00"))],
    "Carl": [(time_to_minutes("09:00"), time_to_minutes("11:00")),
             (time_to_minutes("11:30"), time_to_minutes("12:30")),
             (time_to_minutes("13:00"), time_to_minutes("14:30")),
             (time_to_minutes("15:00"), time_to_minutes("16:00")),
             (time_to_minutes("16:30"), time_to_minutes("17:00"))]
}

# Angela prefers not to have meetings before 15:00. We try to find a meeting time at or after 15:00 if possible.
preferred_start = time_to_minutes("15:00")

def is_slot_free(start, end):
    # Check if the time slot [start, end) is free for all participants.
    for person, intervals in busy.items():
        for busy_start, busy_end in intervals:
            # If the meeting overlaps with a busy interval, it's not free
            if start < busy_end and end > busy_start:
                return False
    return True

# Find a common free slot of meeting_duration minutes
found_slot = None

# Try preferred times first (start time >= 15:00)
for start in range(max(work_start, preferred_start), work_end - meeting_duration + 1):
    end = start + meeting_duration
    if is_slot_free(start, end):
        found_slot = (start, end)
        break

# If no slot was found in the preferred range, search the entire work day
if not found_slot:
    for start in range(work_start, work_end - meeting_duration + 1):
        end = start + meeting_duration
        if is_slot_free(start, end):
            found_slot = (start, end)
            break

if found_slot:
    slot_start, slot_end = found_slot
    meeting_time_range = f"{{{minutes_to_time(slot_start)}:{minutes_to_time(slot_end)}}}"
    print(f"{meeting_time_range} {day}")
else:
    print("No available time slot found.")