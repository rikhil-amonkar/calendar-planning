def time_to_minutes(t):
    # t is string like "10:30"
    h, m = map(int, t.split(':'))
    return (h - 9) * 60 + m

def minutes_to_time(m):
    h = 9 + m // 60
    mm = m % 60
    return f"{h:02d}:{mm:02d}"

def main():
    # Busy intervals in HH:MM format
    stephanie_busy = [("10:00", "10:30"), ("16:00", "16:30")]
    cheryl_busy = [("10:00", "10:30"), ("11:30", "12:00"), ("13:30", "14:00"), ("16:30", "17:00")]
    bradley_busy = [("9:30", "10:00"), ("10:30", "11:30"), ("13:30", "14:00"), ("14:30", "15:00"), ("15:30", "17:00")]
    steven_busy = [("9:00", "12:00"), ("13:00", "13:30"), ("14:30", "17:00")]

    all_schedules = [stephanie_busy, cheryl_busy, bradley_busy, steven_busy]

    # Convert all to minutes from 9:00
    busy_minutes = [False] * 480  # 9:00–17:00 (480 minutes)

    for schedule in all_schedules:
        for start_str, end_str in schedule:
            start_m = time_to_minutes(start_str)
            end_m = time_to_minutes(end_str)
            for t in range(start_m, end_m):
                if t < 480:
                    busy_minutes[t] = True

    # Find free slots of at least 60 minutes
    meeting_length = 60
    free_slots = []
    start = None
    for t in range(480):
        if not busy_minutes[t]:
            if start is None:
                start = t
        else:
            if start is not None:
                if t - start >= meeting_length:
                    free_slots.append((start, t))
                start = None
    if start is not None and 480 - start >= meeting_length:
        free_slots.append((start, 480))

    # Output first suitable slot
    if free_slots:
        start_m, end_m = free_slots[0]
        start_time = minutes_to_time(start_m)
        end_time = minutes_to_time(start_m + meeting_length)
        print(f"Monday {start_time}:{end_time}")
    else:
        print("No suitable slot found")

if __name__ == "__main__":
    main()