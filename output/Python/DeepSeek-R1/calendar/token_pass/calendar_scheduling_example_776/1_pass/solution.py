def main():
    # Convert time to minutes for easier calculation
    def time_to_minutes(time_str):
        hours, minutes = map(int, time_str.split(':'))
        return hours * 60 + minutes

    # Convert minutes to time string
    def minutes_to_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours:02d}:{mins:02d}"

    # Work hours
    work_start = time_to_minutes("09:00")
    work_end = time_to_minutes("17:00")
    meeting_duration = 30

    # John's constraints: free until 14:30 on Monday, entirely free on Tuesday and Wednesday
    john_availability = {
        "Monday": [(work_start, time_to_minutes("14:30"))],
        "Tuesday": [(work_start, work_end)],
        "Wednesday": [(work_start, work_end)]
    }

    # Jennifer's meetings in minutes
    jennifer_meetings = {
        "Monday": [
            (time_to_minutes("09:00"), time_to_minutes("11:00")),
            (time_to_minutes("11:30"), time_to_minutes("13:00")),
            (time_to_minutes("13:30"), time_to_minutes("14:30")),
            (time_to_minutes("15:00"), work_end)
        ],
        "Tuesday": [
            (time_to_minutes("09:00"), time_to_minutes("11:30")),
            (time_to_minutes("12:00"), work_end)
        ],
        "Wednesday": [
            (time_to_minutes("09:00"), time_to_minutes("11:30")),
            (time_to_minutes("12:00"), time_to_minutes("12:30")),
            (time_to_minutes("13:00"), time_to_minutes("14:00")),
            (time_to_minutes("14:30"), time_to_minutes("16:00")),
            (time_to_minutes("16:30"), work_end)
        ]
    }

    # Find free slots for Jennifer each day
    jennifer_free = {}
    for day, meetings in jennifer_meetings.items():
        free_slots = []
        # Start from work start time
        current_time = work_start
        for meeting in sorted(meetings, key=lambda x: x[0]):
            if current_time < meeting[0]:
                free_slots.append((current_time, meeting[0]))
            current_time = meeting[1]
        if current_time < work_end:
            free_slots.append((current_time, work_end))
        jennifer_free[day] = free_slots

    # Find common available time with John
    for day in ["Monday", "Tuesday", "Wednesday"]:
        john_slots = john_availability[day]
        jen_slots = jennifer_free[day]
        for jhn_start, jhn_end in john_slots:
            for jen_start, jen_end in jen_slots:
                # Find overlap
                start = max(jhn_start, jen_start)
                end = min(jhn_end, jen_end)
                if end - start >= meeting_duration:
                    # Found a slot
                    time_range = f"{minutes_to_time(start)}:{minutes_to_time(start + meeting_duration)}"
                    print(f"{day} {time_range}")
                    return

    print("No suitable time found")

if __name__ == "__main__":
    main()