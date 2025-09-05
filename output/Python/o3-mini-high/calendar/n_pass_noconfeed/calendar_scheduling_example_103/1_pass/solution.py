def minutes_to_str(minutes):
    hrs = minutes // 60
    mins = minutes % 60
    return f"{hrs:02d}:{mins:02d}"

# Define working hours and meeting duration (in minutes)
WORK_START = 9 * 60     # 9:00 AM in minutes
WORK_END = 17 * 60      # 17:00 (5:00 PM) in minutes
MEETING_DURATION = 30   # 30 minutes

# Busy intervals for each participant (start and end in minutes)
# Note: end time is exclusive (i.e., a meeting ending at 10:00 means free at 10:00)
diane_busy = [
    (9 * 60 + 30, 10 * 60),   # 09:30 to 10:00
    (14 * 60 + 30, 15 * 60)   # 14:30 to 15:00
]

jack_busy = [
    (13 * 60 + 30, 14 * 60),  # 13:30 to 14:00
    (14 * 60 + 30, 15 * 60)   # 14:30 to 15:00
]

eugene_busy = [
    (9 * 60, 10 * 60),              # 09:00 to 10:00
    (10 * 60 + 30, 11 * 60 + 30),     # 10:30 to 11:30
    (12 * 60, 14 * 60 + 30),          # 12:00 to 14:30
    (15 * 60, 16 * 60 + 30)           # 15:00 to 16:30
]

patricia_busy = [
    (9 * 60 + 30, 10 * 60 + 30),  # 09:30 to 10:30
    (11 * 60, 12 * 60),           # 11:00 to 12:00
    (12 * 60 + 30, 14 * 60),      # 12:30 to 14:00
    (15 * 60, 16 * 60 + 30)       # 15:00 to 16:30
]

# Combine all busy intervals
all_busy = diane_busy + jack_busy + eugene_busy + patricia_busy

def is_slot_free(start_time, duration, busy_intervals):
    end_time = start_time + duration
    # Check for overlap: two intervals [a, b) and [c, d) do not overlap if b <= c or d <= a.
    # So they overlap if start_time < busy_end and end_time > busy_start.
    for busy_start, busy_end in busy_intervals:
        if start_time < busy_end and end_time > busy_start:
            return False
    return True

def find_meeting_slot():
    # Iterate over each minute in the work day where a meeting could start.
    # The latest possible start time is WORK_END - MEETING_DURATION.
    for t in range(WORK_START, WORK_END - MEETING_DURATION + 1):
        if is_slot_free(t, MEETING_DURATION, all_busy):
            return t
    return None

def main():
    slot = find_meeting_slot()
    if slot is not None:
        meeting_start = minutes_to_str(slot)
        meeting_end = minutes_to_str(slot + MEETING_DURATION)
        # Output must include both the time range and the day of the week.
        print(f"Monday {meeting_start}:{meeting_end}")
    else:
        print("No available meeting slot found.")

if __name__ == "__main__":
    main()