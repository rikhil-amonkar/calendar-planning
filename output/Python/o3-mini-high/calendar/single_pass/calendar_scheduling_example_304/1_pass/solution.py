def minutes_to_str(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

# Define meeting parameters
meeting_duration = 30  # minutes
meeting_day = "Monday"
work_start = 9 * 60    # 9:00 in minutes (540)
# Janice prefers meeting to finish by 13:00 so meeting must end by 780 minutes.
latest_meeting_end = 13 * 60  # 13:00 in minutes (780)
latest_start = latest_meeting_end - meeting_duration  # latest possible start

# Define the busy intervals for each participant in minutes from midnight
participants_busy = {
    "Christine": [(9*60+30, 10*60+30), (12*60, 12*60+30), (13*60, 13*60+30), (14*60+30, 15*60), (16*60, 16*60+30)],
    "Janice": [],  # wide open except her preference for before 13:00
    "Bobby": [(12*60, 12*60+30), (14*60+30, 15*60)],
    "Elizabeth": [(9*60, 9*60+30), (11*60+30, 13*60), (13*60+30, 14*60), (15*60, 15*60+30), (16*60, 17*60)],
    "Tyler": [(9*60, 11*60), (12*60, 12*60+30), (13*60, 13*60+30), (15*60+30, 16*60), (16*60+30, 17*60)],
    "Edward": [(9*60, 9*60+30), (10*60, 11*60), (11*60+30, 14*60), (14*60+30, 15*60+30), (16*60, 17*60)]
}

def is_slot_free(start_time):
    """Check if a meeting starting at start_time and lasting meeting_duration is free for all participants."""
    meeting_end = start_time + meeting_duration
    # Ensure meeting finishes by or before 13:00 (Janice's preference)
    if meeting_end > latest_meeting_end:
        return False
    for person, busy_times in participants_busy.items():
        for busy_start, busy_end in busy_times:
            # If the meeting overlaps any busy interval, return False.
            if start_time < busy_end and meeting_end > busy_start:
                return False
    return True

# Find the earliest possible meeting start time in the allowed window
meeting_time = None
for t in range(work_start, latest_start + 1):
    if is_slot_free(t):
        meeting_time = t
        break

if meeting_time is not None:
    meeting_start_str = minutes_to_str(meeting_time)
    meeting_end_str = minutes_to_str(meeting_time + meeting_duration)
    print(meeting_day)
    print(f"{meeting_start_str}:{meeting_end_str}")
else:
    print("No available slot meeting all constraints.")