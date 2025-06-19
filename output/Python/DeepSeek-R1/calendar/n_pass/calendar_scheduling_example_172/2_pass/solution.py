def main():
    # Work hours: 9:00 to 17:00 -> 0 to 480 minutes
    work_start = 0
    work_end = 480
    duration = 30

    # Busy intervals for each participant in minutes (relative to 9:00) as [start, end)
    patrick = [(0, 30), (60, 90), (270, 300), (420, 450)]
    kayla = [(210, 270), (360, 390), (420, 450)]
    carl = [(90, 120), (180, 210), (240, 270), (330, 480)]
    christian = [(0, 210), (240, 300), (330, 480)]
    
    # Combine all busy intervals
    all_busy = patrick + kayla + carl + christian
    
    # Check possible meeting start times (every 30 minutes from work_start to work_end-duration)
    meeting_start = None
    for t in range(work_start, work_end - duration + 1, 30):
        meeting_end = t + duration
        # Check if any busy interval overlaps with [t, meeting_end)
        overlap = False
        for s_busy, e_busy in all_busy:
            if t < e_busy and meeting_end > s_busy:
                overlap = True
                break
        if not overlap:
            meeting_start = t
            break
    
    # Convert and output if found
    if meeting_start is not None:
        start_hour = 9 + meeting_start // 60
        start_minute = meeting_start % 60
        end_time = meeting_start + duration
        end_hour = 9 + end_time // 60
        end_minute = end_time % 60
        time_str = f"{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}"
        print("Monday")
        print(time_str)
    else:
        print("No suitable time found")

if __name__ == "__main__":
    main()