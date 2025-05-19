def find_meeting_time():
    work_start = 9 * 60
    work_end = 17 * 60
    meeting_duration = 30
    nicole_busy = [(9*60, 10*60), (10*60 + 30, 16*60 + 30)]
    nicole_preferred_start = 16 * 60  # 16:00

    # Find free slots after Nicole's preferred start time
    possible_start = max(nicole_preferred_start, nicole_busy[-1][1])
    possible_end = possible_start + meeting_duration

    if possible_end <= work_end:
        return ("Monday", 
                f"{possible_start//60:02d}:{possible_start%60:02d}:"
                f"{possible_end//60:02d}:{possible_end%60:02d}")

day, time_range = find_meeting_time()
print(f"{day}:{time_range}")