def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(":"))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hrs = minutes // 60
    mins = minutes % 60
    return f"{hrs:02d}:{mins:02d}"

def has_conflict(meeting_start, meeting_end, busy_intervals):
    for busy_start, busy_end in busy_intervals:
        # Check if meeting overlaps a busy interval.
        if not (meeting_end <= busy_start or meeting_start >= busy_end):
            return True
    return False

# Busy intervals for each participant on Monday (times in minutes from midnight)
busy_schedules = {
    "Katherine": [(time_to_minutes("12:00"), time_to_minutes("12:30")),
                  (time_to_minutes("13:00"), time_to_minutes("14:30"))],
    "Rebecca": [],  # free all day
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

# Work day boundaries: 9:00 to 17:00 (in minutes)
work_start = time_to_minutes("09:00")
work_end = time_to_minutes("17:00")
meeting_duration = 30  # in minutes

# Angela prefers no meetings before 15:00.
candidate_start = max(work_start, time_to_minutes("15:00"))

found_slot = None

# Check each possible minute between candidate_start and latest possible start time
for start in range(candidate_start, work_end - meeting_duration + 1):
    meeting_start = start
    meeting_end = start + meeting_duration
    # Verify that the meeting fits everyone’s schedule.
    conflict_found = False
    for person, intervals in busy_schedules.items():
        if has_conflict(meeting_start, meeting_end, intervals):
            conflict_found = True
            break
    if not conflict_found:
        found_slot = (meeting_start, meeting_end)
        break

if found_slot:
    start_minutes, end_minutes = found_slot
    time_range = f"{minutes_to_time(start_minutes)}:{minutes_to_time(end_minutes)}"
    print("Monday", time_range)
else:
    print("No suitable meeting time found.")