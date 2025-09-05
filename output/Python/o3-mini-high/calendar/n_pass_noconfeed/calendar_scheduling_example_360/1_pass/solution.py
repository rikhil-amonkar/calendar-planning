def time_to_minutes(t):
    hours, minutes = map(int, t.split(":"))
    return hours * 60 + minutes

def minutes_to_time(m):
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

# Define working hours in minutes (09:00 to 17:00)
work_start = time_to_minutes("09:00")
work_end = time_to_minutes("17:00")
meeting_duration = 30

# Busy schedules per participant (all times in minutes)
schedules = {
    "Emily": [(time_to_minutes("10:00"), time_to_minutes("10:30")),
              (time_to_minutes("16:00"), time_to_minutes("16:30"))],
    "Mason": [],  # free entire day
    "Maria": [(time_to_minutes("10:30"), time_to_minutes("11:00")),
              (time_to_minutes("14:00"), time_to_minutes("14:30"))],
    "Carl": [(time_to_minutes("09:30"), time_to_minutes("10:00")),
             (time_to_minutes("10:30"), time_to_minutes("12:30")),
             (time_to_minutes("13:30"), time_to_minutes("14:00")),
             (time_to_minutes("14:30"), time_to_minutes("15:30")),
             (time_to_minutes("16:00"), time_to_minutes("17:00"))],
    "David": [(time_to_minutes("09:30"), time_to_minutes("11:00")),
              (time_to_minutes("11:30"), time_to_minutes("12:00")),
              (time_to_minutes("12:30"), time_to_minutes("13:30")),
              (time_to_minutes("14:00"), time_to_minutes("15:00")),
              (time_to_minutes("16:00"), time_to_minutes("17:00"))],
    "Frank": [(time_to_minutes("09:30"), time_to_minutes("10:30")),
              (time_to_minutes("11:00"), time_to_minutes("11:30")),
              (time_to_minutes("12:30"), time_to_minutes("13:30")),
              (time_to_minutes("14:30"), time_to_minutes("17:00"))]
}

day = "Monday"

def is_free(meeting_start, meeting_end, busy_times):
    for busy_start, busy_end in busy_times:
        # Check if meeting overlaps any busy interval
        if meeting_start < busy_end and meeting_end > busy_start:
            return False
    return True

# Try every possible start time (each minute) within working hours 
# until a slot is found where everyone is available.
meeting_time_found = False
meeting_start_time = None

for candidate_start in range(work_start, work_end - meeting_duration + 1):
    candidate_end = candidate_start + meeting_duration
    conflict = False
    for person, busy_times in schedules.items():
        if not is_free(candidate_start, candidate_end, busy_times):
            conflict = True
            break
    if not conflict:
        meeting_start_time = candidate_start
        meeting_time_found = True
        break

if meeting_time_found:
    start_str = minutes_to_time(meeting_start_time)
    end_str = minutes_to_time(meeting_start_time + meeting_duration)
    # Output in the format HH:MM:HH:MM along with the day of the week.
    print(f"{start_str}:{end_str} {day}")
else:
    print("No available meeting time found.")