def main():
    # Convert time strings to minutes since midnight for easier calculation
    def time_to_minutes(time_str):
        hours, minutes = map(int, time_str.split(':'))
        return hours * 60 + minutes

    def minutes_to_time(minutes):
        hours = minutes // 60
        minutes = minutes % 60
        return f"{hours:02d}:{minutes:02d}"

    # Work hours
    work_start = time_to_minutes("09:00")
    work_end = time_to_minutes("17:00")
    meeting_duration = 30  # minutes

    # Eric's blocked times in minutes
    eric_blocked = [
        (time_to_minutes("12:00"), time_to_minutes("13:00")),
        (time_to_minutes("14:00"), time_to_minutes("15:00"))
    ]

    # Henry's meetings in minutes
    henry_meetings = [
        (time_to_minutes("09:30"), time_to_minutes("10:00")),
        (time_to_minutes("10:30"), time_to_minutes("11:00")),
        (time_to_minutes("11:30"), time_to_minutes("12:30")),
        (time_to_minutes("13:00"), time_to_minutes("13:30")),
        (time_to_minutes("14:30"), time_to_minutes("15:00")),
        (time_to_minutes("16:00"), time_to_minutes("17:00"))
    ]

    # Generate free intervals for Eric within work hours
    eric_free = []
    current = work_start
    for start, end in sorted(eric_blocked):
        if current < start:
            eric_free.append((current, start))
        current = end
    if current < work_end:
        eric_free.append((current, work_end))

    # Generate free intervals for Henry within work hours
    henry_free = []
    current = work_start
    for start, end in sorted(henry_meetings):
        if current < start:
            henry_free.append((current, start))
        current = end
    if current < work_end:
        henry_free.append((current, work_end))

    # Find earliest available slot that fits both schedules and respects Henry's preference
    meeting_slot = None
    for h_start, h_end in henry_free:
        # Check if this interval is before 10:00 (Henry's preference)
        if h_end <= time_to_minutes("10:00"):
            for e_start, e_end in eric_free:
                # Find overlap between Henry's free interval and Eric's free interval
                overlap_start = max(h_start, e_start)
                overlap_end = min(h_end, e_end)
                if overlap_start < overlap_end:
                    available_duration = overlap_end - overlap_start
                    if available_duration >= meeting_duration:
                        meeting_slot = (overlap_start, overlap_start + meeting_duration)
                        break
            if meeting_slot:
                break

    # If no slot found before 10:00, check all intervals
    if not meeting_slot:
        for h_start, h_end in henry_free:
            for e_start, e_end in eric_free:
                overlap_start = max(h_start, e_start)
                overlap_end = min(h_end, e_end)
                if overlap_start < overlap_end:
                    available_duration = overlap_end - overlap_start
                    if available_duration >= meeting_duration:
                        meeting_slot = (overlap_start, overlap_start + meeting_duration)
                        break
            if meeting_slot:
                break

    # Output the meeting time
    start_time = minutes_to_time(meeting_slot[0])
    end_time = minutes_to_time(meeting_slot[1])
    print(f"{start_time}:{end_time}")
    print("Monday")

if __name__ == "__main__":
    main()