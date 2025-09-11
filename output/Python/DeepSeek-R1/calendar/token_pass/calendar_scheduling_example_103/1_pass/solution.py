def time_str_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return (hours - 9) * 60 + minutes

def minutes_to_time_str(minutes):
    total_minutes = minutes
    hours = 9 + total_minutes // 60
    mins = total_minutes % 60
    return f"{hours:02d}:{mins:02d}"

def main():
    work_start = time_str_to_minutes("9:00")
    work_end = time_str_to_minutes("17:00")
    total_minutes = work_end - work_start
    available = [True] * total_minutes

    blocked_intervals = [
        # Diane's blocked intervals
        [("9:30", "10:00"), ("14:30", "15:00")],
        # Jack's blocked intervals
        [("13:30", "14:00"), ("14:30", "15:00")],
        # Eugene's blocked intervals
        [("9:00", "10:00"), ("10:30", "11:30"), ("12:00", "14:30"), ("15:00", "16:30")],
        # Patricia's blocked intervals
        [("9:30", "10:30"), ("11:00", "12:00"), ("12:30", "14:00"), ("15:00", "16:30")]
    ]

    for person_blocks in blocked_intervals:
        for start_str, end_str in person_blocks:
            start_min = time_str_to_minutes(start_str)
            end_min = time_str_to_minutes(end_str)
            for minute in range(start_min, end_min):
                if minute < total_minutes:
                    available[minute] = False

    meeting_duration = 30
    found_slot = False
    start_minute = 0
    for start in range(total_minutes - meeting_duration + 1):
        if all(available[start + i] for i in range(meeting_duration)):
            start_minute = start
            found_slot = True
            break

    if found_slot:
        start_time = minutes_to_time_str(start_minute)
        end_time = minutes_to_time_str(start_minute + meeting_duration)
        print(f"Monday {start_time}:{end_time}")
    else:
        print("No suitable time slot found.")

if __name__ == "__main__":
    main()