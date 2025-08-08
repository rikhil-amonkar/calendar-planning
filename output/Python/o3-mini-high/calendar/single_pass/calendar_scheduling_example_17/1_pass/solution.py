def minutes_to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def is_slot_available(start, duration, busy_intervals):
    end = start + duration
    # Check if the proposed meeting [start, end) overlaps with any busy interval.
    for busy_start, busy_end in busy_intervals:
        # If meeting starts before busy_end and ends after busy_start, they overlap.
        if start < busy_end and end > busy_start:
            return False
    return True

def main():
    meeting_duration = 30  # minutes
    # Work hours for Monday: 9:00 (540 minutes) to 17:00 (1020 minutes)
    # Due to Helen's constraint (no meetings after 13:30, i.e. 810 minutes),
    # the meeting must end by 13:30.
    work_start = 9 * 60      # 540
    latest_meeting_end = 13 * 60 + 30  # 810, so latest start is 810 - 30 = 780 minutes

    # Margaret's busy intervals (in minutes since midnight)
    margaret_busy = [
        (9 * 60, 10 * 60),         # 9:00 - 10:00 -> (540, 600)
        (10 * 60 + 30, 11 * 60),     # 10:30 - 11:00 -> (630, 660)
        (11 * 60 + 30, 12 * 60),     # 11:30 - 12:00 -> (690, 720)
        (13 * 60, 13 * 60 + 30),     # 13:00 - 13:30 -> (780, 810)
        (15 * 60, 15 * 60 + 30)      # 15:00 - 15:30 -> (900, 930)
    ]
    
    # Donna's busy intervals (though they fall later in the day, included for completeness)
    donna_busy = [
        (14 * 60 + 30, 15 * 60),     # 14:30 - 15:00 -> (870, 900)
        (16 * 60, 16 * 60 + 30)      # 16:00 - 16:30 -> (960, 990)
    ]
    
    # Helen's busy intervals
    helen_busy = [
        (9 * 60, 9 * 60 + 30),       # 9:00 - 9:30 -> (540, 570)
        (10 * 60, 11 * 60 + 30),     # 10:00 - 11:30 -> (600, 690)
        (13 * 60, 14 * 60),          # 13:00 - 14:00 -> (780, 840)
        (14 * 60 + 30, 15 * 60),     # 14:30 - 15:00 -> (870, 900)
        (15 * 60 + 30, 17 * 60)      # 15:30 - 17:00 -> (930, 1020)
    ]
    
    meeting_day = "Monday"
    
    # Iterate minute-by-minute starting from work_start to the latest valid start time.
    for start in range(work_start, latest_meeting_end - meeting_duration + 1):
        # Ensure the meeting ends by 13:30.
        end = start + meeting_duration
        if end > latest_meeting_end:
            break
        if (is_slot_available(start, meeting_duration, margaret_busy) and
            is_slot_available(start, meeting_duration, donna_busy) and
            is_slot_available(start, meeting_duration, helen_busy)):
            meeting_start_str = minutes_to_time_str(start)
            meeting_end_str = minutes_to_time_str(end)
            # Output in the format HH:MM:HH:MM and the day of the week.
            print(f"{meeting_start_str}:{meeting_end_str} {meeting_day}")
            return
            
    print("No available common slot found.")

if __name__ == "__main__":
    main()