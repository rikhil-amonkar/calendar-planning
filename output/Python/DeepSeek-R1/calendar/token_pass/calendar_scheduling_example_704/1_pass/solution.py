def main():
    # Define work hours in minutes from midnight
    work_start = 9 * 60  # 09:00
    work_end = 17 * 60   # 17:00
    meeting_duration = 30

    # Samuel's busy times in minutes from midnight for each day
    samuel_busy = {
        'Monday': [
            (10*60+30, 11*60),    # 10:30-11:00
            (12*60, 12*60+30),     # 12:00-12:30
            (13*60, 15*60),        # 13:00-15:00
            (15*60+30, 16*60+30)   # 15:30-16:30
        ],
        'Tuesday': [
            (9*60, 12*60),         # 09:00-12:00
            (14*60, 15*60+30),     # 14:00-15:30
            (16*60+30, 17*60)      # 16:30-17:00
        ],
        'Wednesday': [
            (10*60+30, 11*60),     # 10:30-11:00
            (11*60+30, 12*60),     # 11:30-12:00
            (12*60+30, 13*60),     # 12:30-13:00
            (14*60, 14*60+30),     # 14:00-14:30
            (15*60, 16*60)         # 15:00-16:00
        ]
    }

    # Preferred day order considering constraints
    days = ['Monday', 'Tuesday', 'Wednesday']

    for day in days:
        busy_times = samuel_busy[day]
        busy_times.sort(key=lambda x: x[0])  # Sort by start time
        free_slots = []
        current = work_start

        # Calculate free slots between busy intervals
        for start, end in busy_times:
            if current < start:
                free_slots.append((current, start))
            current = max(current, end)
        if current < work_end:
            free_slots.append((current, work_end))

        # Find first suitable slot
        for start, end in free_slots:
            if end - start >= meeting_duration:
                meeting_start = start
                meeting_end = meeting_start + meeting_duration
                # Convert minutes to HH:MM format
                start_str = f"{meeting_start//60:02d}:{meeting_start%60:02d}"
                end_str = f"{meeting_end//60:02d}:{meeting_end%60:02d}"
                print(f"{day}")
                print(f"{start_str}:{end_str}")
                return

    # Fallback if no slot found (shouldn't happen per problem statement)
    print("No suitable time found")

if __name__ == "__main__":
    main()