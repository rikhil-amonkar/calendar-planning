def convert_minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"


def get_free_intervals(busy_intervals, work_start=540, work_end=1020):
    sorted_busy = sorted(busy_intervals, key=lambda x: x[0])
    available = [(work_start, work_end)]
    for start, end in sorted_busy:
        new_available = []
        for a_start, a_end in available:
            if end <= a_start:
                new_available.append((a_start, a_end))
            elif start >= a_end:
                new_available.append((a_start, a_end))
            else:
                if a_start < start:
                    new_available.append((a_start, start))
                if a_end > end:
                    new_available.append((end, a_end))
        available = new_available
    return available


def find_meeting_time():
    natalie_busy = {
        'Monday': [
            (9*60, 9*60 + 30),
            (10*60, 12*60),
            (12*60 + 30, 13*60),
            (14*60, 14*60 + 30),
            (15*60, 16*60 + 30)
        ],
        'Tuesday': [
            (9*60, 9*60 + 30),
            (10*60, 10*60 + 30),
            (12*60 + 30, 14*60),
            (16*60, 17*60)
        ],
        'Wednesday': [
            (11*60, 11*60 + 30),
            (16*60, 16*60 + 30)
        ],
        'Thursday': [
            (10*60, 11*60),
            (11*60 + 30, 15*60),
            (15*60 + 30, 16*60),
            (16*60 + 30, 17*60)
        ]
    }
    
    william_busy = {
        'Monday': [
            (9*60 + 30, 11*60),
            (11*60 + 30, 17*60)
        ],
        'Tuesday': [
            (9*60, 13*60),
            (13*60 + 30, 16*60)
        ],
        'Wednesday': [
            (9*60, 12*60 + 30),
            (13*60, 14*60 + 30),
            (15*60 + 30, 16*60),
            (16*60 + 30, 17*60)
        ],
        'Thursday': [
            (9*60, 10*60 + 30),
            (11*60, 11*60 + 30),
            (12*60, 12*60 + 30),
            (13*60, 14*60),
            (15*60, 17*60)
        ]
    }
    
    days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday']
    for day in days:
        natalie_free = get_free_intervals(natalie_busy[day])
        william_free = get_free_intervals(william_busy[day])
        for n_start, n_end in natalie_free:
            for w_start, w_end in william_free:
                overlap_start = max(n_start, w_start)
                overlap_end = min(n_end, w_end)
                if overlap_end - overlap_start >= 60:
                    start_time = convert_minutes_to_time(overlap_start)
                    end_time = convert_minutes_to_time(overlap_end)
                    print(f"{day} {start_time}:{end_time}")
                    return


find_meeting_time()
