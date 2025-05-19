def find_meeting_time():
    # Define work hours and meeting duration
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    meeting_duration = 30

    # Convert all schedules to minute-based blocks
    schedules = {
        'Andrea': [],
        'Jack': [(9*60, 9*60+30), (14*60, 14*60+30)],
        'Madison': [(9*60+30, 10*60+30), (13*60, 14*60), (15*60, 15*60+30), (16*60+30, 17*60)],
        'Rachel': [(9*60+30, 10*60+30), (11*60, 11*60+30), (12*60, 13*60+30), (14*60+30, 15*60+30), (16*60, 17*60)],
        'Douglas': [(9*60, 11*60+30), (12*60, 16*60+30)],
        'Ryan': [(9*60, 9*60+30), (13*60, 14*60), (14*60+30, 17*60)]
    }

    # Find free slots for all participants
    for start in range(work_start, work_end - meeting_duration + 1):
        end = start + meeting_duration
        if all(
            not any(s_start <= start < s_end or s_start < end <= s_end for s_start, s_end in person_schedule)
            for person_schedule in schedules.values()
        ):
            # Convert back to HH:MM format
            return f"{start//60:02}:{start%60:02}-{end//60:02}:{end%60:02}"

    return None

result = find_meeting_time()
print(f"Monday {result.replace('-', ':')}")