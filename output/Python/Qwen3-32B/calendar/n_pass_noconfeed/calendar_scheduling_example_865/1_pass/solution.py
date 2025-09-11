def time_str_to_min(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def get_free_intervals(busy_intervals):
    sorted_busy = sorted(busy_intervals, key=lambda x: x[0])
    free = []
    current_start = 9 * 60  # 9:00 AM
    for start, end in sorted_busy:
        if start > current_start:
            free.append((current_start, start))
        current_start = max(current_start, end)
    if current_start < 17 * 60:  # 5:00 PM
        free.append((current_start, 17 * 60))
    return free

def main():
    megan_days = {
        'Monday': [('13:00', '13:30'), ('14:00', '15:30')],
        'Tuesday': [('9:00', '9:30'), ('12:00', '12:30'), ('16:00', '17:00')],
        'Wednesday': [('9:30', '10:00'), ('10:30', '11:30'), ('12:30', '14:00'), ('16:00', '16:30')],
        'Thursday': [('13:30', '14:30'), ('15:00', '15:30')],
    }

    daniel_days = {
        'Monday': [('10:00', '11:30'), ('12:30', '15:00')],
        'Tuesday': [('9:00', '10:00'), ('10:30', '17:00')],
        'Wednesday': [('9:00', '10:00'), ('10:30', '11:30'), ('12:00', '17:00')],
        'Thursday': [('9:00', '12:00'), ('12:30', '14:30'), ('15:00', '15:30'), ('16:00', '17:00')],
    }

    days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday']
    for day in days:
        megan_busy = [(time_str_to_min(s), time_str_to_min(e)) for s, e in megan_days.get(day, [])]
        daniel_busy = [(time_str_to_min(s), time_str_to_min(e)) for s, e in daniel_days.get(day, [])]
        megan_free = get_free_intervals(megan_busy)
        daniel_free = get_free_intervals(daniel_busy)
        for m_start, m_end in megan_free:
            for d_start, d_end in daniel_free:
                overlap_start = max(m_start, d_start)
                overlap_end = min(m_end, d_end)
                if overlap_start < overlap_end and (overlap_end - overlap_start) >= 60:
                    start_h = overlap_start // 60
                    start_m = overlap_start % 60
                    end_h = overlap_end // 60
                    end_m = overlap_end % 60
                    start_time = f"{start_h:02d}:{start_m:02d}"
                    end_time = f"{end_h:02d}:{end_m:02d}"
                    print(f"{start_time}:{end_time} {day}")
                    return

if __name__ == "__main__":
    main()