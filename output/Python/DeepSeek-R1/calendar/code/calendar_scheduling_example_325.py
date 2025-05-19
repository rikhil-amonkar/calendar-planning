def find_meeting_time():
    work_start = 9 * 60
    work_end = 17 * 60
    duration = 30
    participants = {
        'Jose': [(11*60, 11*60+30), (12*60+30, 13*60)],
        'Keith': [(14*60, 14*60+30), (15*60, 15*60+30)],
        'Logan': [(9*60, 10*60), (12*60, 12*60+30), (15*60, 15*60+30)],
        'Megan': [(9*60, 10*60+30), (11*60, 12*60), (13*60, 13*60+30), (14*60+30, 16*60+30)],
        'Gary': [(9*60, 9*60+30), (10*60, 10*60+30), (11*60+30, 13*60), (13*60+30, 14*60), (14*60+30, 16*60+30)],
        'Bobby': [(11*60, 11*60+30), (12*60, 12*60+30), (13*60, 16*60)]
    }
    jose_max_end = 15 * 60 + 30  # 15:30 latest end time

    for start in range(work_start, work_end - duration + 1, 5):
        end = start + duration
        if end > jose_max_end:
            continue
        all_available = True
        for busy in participants.values():
            for s, e in busy:
                if not (end <= s or start >= e):
                    all_available = False
                    break
            if not all_available:
                break
        if all_available:
            return f"{start//60:02d}:{start%60:02d}-{end//60:02d}:{end%60:02d}", "Monday"
    return None

meeting_time, day = find_meeting_time()
if meeting_time:
    start, end = meeting_time.split('-')
    start_h, start_m = map(int, start.split(':'))
    end_h, end_m = map(int, end.split(':'))
    print(f"{day} {start_h:02d}:{start_m:02d}-{end_h:02d}:{end_m:02d}")
else:
    print("No suitable time found")