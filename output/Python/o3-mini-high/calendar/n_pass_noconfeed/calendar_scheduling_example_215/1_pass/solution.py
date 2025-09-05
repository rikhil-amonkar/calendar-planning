#!/usr/bin/env python3
def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def has_conflict(meeting_start, meeting_end, busy_intervals):
    # Two intervals [a,b) and [c,d) conflict if a < d and c < b.
    for busy_start, busy_end in busy_intervals:
        if meeting_start < busy_end and busy_start < meeting_end:
            return True
    return False

def meeting_possible(meeting_start, duration, all_schedules):
    meeting_end = meeting_start + duration
    for busy_intervals in all_schedules.values():
        if has_conflict(meeting_start, meeting_end, busy_intervals):
            return False
    return True

def main():
    # Define working hours in minutes from midnight.
    work_start = 9 * 60   # 09:00 => 540 minutes
    work_end = 17 * 60    # 17:00 => 1020 minutes
    meeting_duration = 30 # duration in minutes

    # Define each participant's busy intervals (in minutes from midnight).
    # Each interval is represented as [start, end) so that touching intervals do not conflict.
    schedules = {
        "Steven": [],
        "Roy": [],
        "Cynthia": [
            (9 * 60 + 30, 10 * 60 + 30),  # 09:30 to 10:30
            (11 * 60 + 30, 12 * 60),      # 11:30 to 12:00
            (13 * 60, 13 * 60 + 30),      # 13:00 to 13:30
            (15 * 60, 16 * 60)            # 15:00 to 16:00
        ],
        "Lauren": [
            (9 * 60, 9 * 60 + 30),        # 09:00 to 09:30
            (10 * 60 + 30, 11 * 60),       # 10:30 to 11:00
            (11 * 60 + 30, 12 * 60),       # 11:30 to 12:00
            (13 * 60, 13 * 60 + 30),       # 13:00 to 13:30
            (14 * 60, 14 * 60 + 30),       # 14:00 to 14:30
            (15 * 60, 15 * 60 + 30),       # 15:00 to 15:30
            (16 * 60, 17 * 60)            # 16:00 to 17:00
        ],
        "Robert": [
            (10 * 60 + 30, 11 * 60),      # 10:30 to 11:00
            (11 * 60 + 30, 12 * 60),      # 11:30 to 12:00
            (12 * 60 + 30, 13 * 60 + 30),  # 12:30 to 13:30
            (14 * 60, 16 * 60)            # 14:00 to 16:00
        ]
    }

    # Find the earliest slot within working hours where a meeting can be scheduled.
    meeting_slot = None
    # We iterate every minute from work_start to latest possible start so that meeting fits.
    for start in range(work_start, work_end - meeting_duration + 1):
        if meeting_possible(start, meeting_duration, schedules):
            meeting_slot = (start, start + meeting_duration)
            break

    if meeting_slot:
        start_str = minutes_to_time(meeting_slot[0])
        end_str = minutes_to_time(meeting_slot[1])
        # Output the day and the time range in the specified format.
        print("Monday")
        print(f"{start_str}:{end_str}")
    else:
        print("No available time slot found.")

if __name__ == "__main__":
    main()