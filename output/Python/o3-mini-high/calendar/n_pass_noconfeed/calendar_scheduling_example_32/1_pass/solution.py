def to_minutes(time_str):
    hours, minutes = map(int, time_str.split(":"))
    return hours * 60 + minutes

def to_hhmm(minutes):
    return f"{minutes // 60:02d}:{minutes % 60:02d}"

# Meeting and work hours configuration
meeting_duration = 30  # minutes
day = "Monday"
work_start = to_minutes("09:00")
work_end = to_minutes("17:00")
# Frank's constraint: meeting must end by 09:30 on Monday.
frank_latest_end = to_minutes("09:30")

# Existing busy schedules (start, end) in minutes
emily_busy = [
    (to_minutes("10:00"), to_minutes("10:30")),
    (to_minutes("11:30"), to_minutes("12:30")),
    (to_minutes("14:00"), to_minutes("15:00")),
    (to_minutes("16:00"), to_minutes("16:30"))
]

melissa_busy = [
    (to_minutes("09:30"), to_minutes("10:00")),
    (to_minutes("14:30"), to_minutes("15:00"))
]

frank_busy = [
    (to_minutes("10:00"), to_minutes("10:30")),
    (to_minutes("11:00"), to_minutes("11:30")),
    (to_minutes("12:30"), to_minutes("13:00")),
    (to_minutes("13:30"), to_minutes("14:30")),
    (to_minutes("15:00"), to_minutes("16:00")),
    (to_minutes("16:30"), to_minutes("17:00"))
]

# Helper function to check if two time intervals overlap
def overlaps(start, end, interval):
    busy_start, busy_end = interval
    return not (end <= busy_start or start >= busy_end)

# Determine the latest possible start time given all constraints:
# The meeting must finish by frank_latest_end, so candidate start must be <= frank_latest_end - meeting_duration.
latest_start = min(work_end - meeting_duration, frank_latest_end - meeting_duration)

found_slot = False
candidate_start = work_start

# Since the window is very narrow because of Frank's constraint,
# we increment candidate_start in minute-steps
while candidate_start <= latest_start:
    candidate_end = candidate_start + meeting_duration
    
    # Ensure meeting does not go past Frank's latest acceptable time
    if candidate_end > frank_latest_end:
        candidate_start += 1
        continue

    conflict = False
    # Check Emily's schedule
    for interval in emily_busy:
        if overlaps(candidate_start, candidate_end, interval):
            conflict = True
            break
    if conflict:
        candidate_start += 1
        continue

    # Check Melissa's schedule
    for interval in melissa_busy:
        if overlaps(candidate_start, candidate_end, interval):
            conflict = True
            break
    if conflict:
        candidate_start += 1
        continue

    # Check Frank's busy intervals
    for interval in frank_busy:
        if overlaps(candidate_start, candidate_end, interval):
            conflict = True
            break
    if conflict:
        candidate_start += 1
        continue

    # Found a valid meeting slot
    found_slot = True
    break

if found_slot:
    start_time_str = to_hhmm(candidate_start)
    end_time_str = to_hhmm(candidate_start + meeting_duration)
    print(f"{start_time_str}:{end_time_str}")
    print(day)
else:
    print("No available slot meeting all constraints.")