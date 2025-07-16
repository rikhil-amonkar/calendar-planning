def main():
    total_minutes_in_work_day = 480  # 9:00 to 17:00 is 8 hours = 480 minutes
    free = [True] * total_minutes_in_work_day  # Represents 0 to 479 minutes (9:00 to 16:59)

    participants = [
        ("Tyler", ""),
        ("Kelly", ""),
        ("Stephanie", "11:00 to 11:30, 14:30 to 15:00;"),
        ("Hannah", ""),
        ("Joe", "9:00 to 9:30, 10:00 to 12:00, 12:30 to 13:00, 14:00 to 17:00;"),
        ("Diana", "9:00 to 10:30, 11:30 to 12:00, 13:00 to 14:00, 14:30 to 15:30, 16:00 to 17:00;"),
        ("Deborah", "9:00 to 10:00, 10:30 to 12:00, 12:30 to 13:00, 13:30 to 14:00, 14:30 to 15:30, 16:00 to 16:30;")
    ]

    def time_str_to_minutes(time_str):
        hour, minute = map(int, time_str.split(':'))
        return (hour - 9) * 60 + minute

    for name, busy_str in participants:
        if not busy_str.strip():
            continue
        busy_intervals = busy_str.strip().rstrip(';').split(',')
        for interval in busy_intervals:
            interval = interval.strip()
            if not interval:
                continue
            parts = interval.split(' to ')
            if len(parts) < 2:
                continue
            start_str, end_str = parts[0].strip(), parts[1].strip()
            try:
                start_min = time_str_to_minutes(start_str)
                end_min = time_str_to_minutes(end_str)
            except:
                continue
            if start_min >= total_minutes_in_work_day:
                continue
            end_index = min(end_min, total_minutes_in_work_day)
            for minute in range(start_min, end_index):
                if minute < total_minutes_in_work_day:
                    free[minute] = False

    required_minutes = 30
    consecutive_free = 0
    start_slot = -1
    for minute in range(total_minutes_in_work_day):
        if free[minute]:
            consecutive_free += 1
            if consecutive_free >= required_minutes:
                start_slot = minute - required_minutes + 1
                break
        else:
            consecutive_free = 0

    # Convert start slot to time
    total_minutes_start = start_slot
    start_hour = 9 + total_minutes_start // 60
    start_minute_val = total_minutes_start % 60
    end_minutes = total_minutes_start + required_minutes
    end_hour = 9 + end_minutes // 60
    end_minute_val = end_minutes % 60

    time_range_str = f"{start_hour}:{start_minute_val:02d}:{end_hour}:{end_minute_val:02d}"
    print("Monday")
    print(time_range_str)

if __name__ == "__main__":
    main()