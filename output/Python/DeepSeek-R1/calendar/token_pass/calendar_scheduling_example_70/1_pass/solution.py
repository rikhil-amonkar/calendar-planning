def main():
    # Define work hours (9:00 to 17:00) in minutes since 9:00
    work_start = 0   # 9:00
    work_end = 480   # 17:00 (8 hours * 60 minutes)
    duration = 30

    # Busy intervals in minutes since 9:00 (start inclusive, end exclusive)
    denise_busy = [(180, 210), (390, 420)]  # 12:00-12:30, 15:30-16:00
    natalie_busy = [(0, 150), (180, 240), (300, 330), (360, 480)]  # 9:00-11:30, 12:00-13:00, 14:00-14:30, 15:00-17:00
    # Angela has no meetings

    # Create a free/busy array for all participants (480 minutes, initially free)
    free_slots = [True] * work_end  # Index 0 to 479

    # Mark busy minutes for Denise
    for start, end in denise_busy:
        for minute in range(start, end):
            if minute < work_end:
                free_slots[minute] = False

    # Mark busy minutes for Natalie
    for start, end in natalie_busy:
        for minute in range(start, end):
            if minute < work_end:
                free_slots[minute] = False

    # Find earliest available slot of duration minutes
    start_minute = None
    for i in range(work_end - duration + 1):
        if all(free_slots[i + j] for j in range(duration)):
            start_minute = i
            break

    if start_minute is None:
        print("No suitable time found")
        return

    # Convert start_minute to time format
    start_hour = 9 + start_minute // 60
    start_min = start_minute % 60
    end_minute = start_minute + duration
    end_hour = 9 + end_minute // 60
    end_min = end_minute % 60

    # Format the output
    time_str = f"{start_hour:02d}:{start_min:02d}:{end_hour:02d}:{end_min:02d}"
    print(f"{time_str}")
    print("Monday")

if __name__ == "__main__":
    main()