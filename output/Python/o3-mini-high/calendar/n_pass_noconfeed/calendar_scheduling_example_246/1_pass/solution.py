import datetime

def minutes_to_time(minutes):
    # Our workday starts at 9:00. Add minutes to 9:00 to get the real time.
    base = datetime.datetime(2021, 1, 1, 9, 0)
    time_point = base + datetime.timedelta(minutes=minutes)
    return time_point.strftime("%H:%M")

def has_conflict(start, end, intervals):
    # Returns True if the candidate interval [start, end) overlaps any busy interval.
    for busy_start, busy_end in intervals:
        # Overlap exists if candidate start is before a busy end
        # and candidate end is after busy start.
        if start < busy_end and end > busy_start:
            return True
    return False

# Define busy intervals for each participant in minutes relative to 9:00.
busy_schedules = {
    "Jacob": [(270, 300), (330, 360)],  # 13:30-14:00, 14:30-15:00
    "Diana": [(30, 60), (150, 180), (240, 270), (420, 450)],  # 9:30-10:00, 11:30-12:00, 13:00-13:30, 16:00-16:30
    "Adam": [(30, 90), (120, 210), (390, 420)],  # 9:30-10:30, 11:00-12:30, 15:30-16:00
    "Angela": [(30, 60), (90, 180), (240, 390), (420, 450)],  # 9:30-10:00, 10:30-12:00, 13:00-15:30, 16:00-16:30
    "Dennis": [(0, 30), (90, 150), (240, 360), (450, 480)]  # 9:00-9:30, 10:30-11:30, 13:00-15:00, 16:30-17:00
}

meeting_duration = 30  # minutes
work_start = 0         # 9:00 in minutes relative to 9:00
work_end = 480         # 17:00 is 480 minutes after 9:00

# Find the earliest 30-minute slot that is free for everyone.
meeting_slot = None

for candidate_start in range(work_start, work_end - meeting_duration + 1):
    candidate_end = candidate_start + meeting_duration
    conflict_found = False
    for person, intervals in busy_schedules.items():
        if has_conflict(candidate_start, candidate_end, intervals):
            conflict_found = True
            break
    if not conflict_found:
        meeting_slot = (candidate_start, candidate_end)
        break

if meeting_slot:
    start_minutes, end_minutes = meeting_slot
    start_time_str = minutes_to_time(start_minutes)
    end_time_str = minutes_to_time(end_minutes)
    day = "Monday"
    # Output in the format "Day HH:MM:HH:MM" where the time range is start:end.
    print(f"{day} {start_time_str}:{end_time_str}")
else:
    print("No available slot found.")