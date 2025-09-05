def time_to_minutes(t):
    # Convert HH:MM string to minutes from midnight
    hours, minutes = map(int, t.split(':'))
    return hours * 60 + minutes

def minutes_to_time(m):
    # Convert minutes from midnight to HH:MM string (zero-padded)
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

def slot_overlaps(slot_start, slot_end, busy_start, busy_end):
    # Two intervals [slot_start, slot_end) and [busy_start, busy_end) overlap if:
    # slot_start < busy_end and busy_start < slot_end.
    return slot_start < busy_end and busy_start < slot_end

def is_slot_free(start, duration, busy_times):
    end = start + duration
    for b_start, b_end in busy_times:
        if slot_overlaps(start, end, b_start, b_end):
            return False
    return True

# Meeting details
meeting_duration = 30  # in minutes
# Work hours for the meeting. Note: due to Harold's preference the meeting must end by 13:00.
work_start = time_to_minutes("09:00")
work_end = time_to_minutes("13:00")  # meeting must finish by 13:00

# Busy intervals for each participant (all intervals in HH:MM format)
participants_busy_str = {
    "Jacqueline": [("09:00", "09:30"), ("11:00", "11:30"), ("12:30", "13:00"), ("15:30", "16:00")],
    "Harold":     [("10:00", "10:30"), ("13:00", "13:30"), ("15:00", "17:00")],
    "Arthur":     [("09:00", "09:30"), ("10:00", "12:30"), ("14:30", "15:00"), ("15:30", "17:00")],
    "Kelly":      [("09:00", "09:30"), ("10:00", "11:00"), ("11:30", "12:30"), ("14:00", "15:00"), ("15:30", "16:00")]
}

# Convert busy times to minutes, keeping only intervals that might affect the morning meeting
participants_busy = {}
for person, intervals in participants_busy_str.items():
    busy_intervals = []
    for start_str, end_str in intervals:
        start = time_to_minutes(start_str)
        end = time_to_minutes(end_str)
        # Only consider overlaps within the work window [work_start, work_end].
        if end <= work_start or start >= work_end:
            continue
        # Clip the busy interval to the working window if needed.
        busy_intervals.append((max(start, work_start), min(end, work_end)))
    participants_busy[person] = busy_intervals

# Since Harold does not want to meet after 13:00, we only search for slots within [09:00, 13:00 - meeting_duration]
latest_start = work_end - meeting_duration

# Search minute-by-minute for a common free slot for all participants.
meeting_start = None
for t in range(work_start, latest_start + 1):
    slot_ok = True
    for busy_times in participants_busy.values():
        if not is_slot_free(t, meeting_duration, busy_times):
            slot_ok = False
            break
    if slot_ok:
        meeting_start = t
        break

# Output the meeting time if found
if meeting_start is not None:
    meeting_end = meeting_start + meeting_duration
    start_str = minutes_to_time(meeting_start)
    end_str = minutes_to_time(meeting_end)
    # Output the day and the meeting time in the format {HH:MM:HH:MM}
    print("Monday", f"{{{start_str}:{end_str}}}")
else:
    print("No common available slot found.")