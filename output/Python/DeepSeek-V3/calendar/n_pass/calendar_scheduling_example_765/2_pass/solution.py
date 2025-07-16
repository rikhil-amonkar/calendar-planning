def find_meeting_time():
    # Define work hours and days to consider
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60    # 17:00 in minutes
    days = ['Monday', 'Tuesday', 'Wednesday']
    meeting_duration = 30  # minutes

    # Define busy times for Joshua and Joyce in minutes since midnight
    joshua_busy = {
        'Monday': [(15 * 60, 15 * 60 + 30)],
        'Tuesday': [(11 * 60 + 30, 12 * 60), (13 * 60, 13 * 60 + 30), (14 * 60 + 30, 15 * 60)],
        'Wednesday': []
    }
    
    joyce_busy = {
        'Monday': [(0, 12 * 60), (13 * 60, 15 * 60), (15 * 60 + 30, 17 * 60)],  # Updated to reflect Joyce's unavailability before 12:00
        'Tuesday': [(9 * 60, 17 * 60)],
        'Wednesday': [(9 * 60, 9 * 60 + 30), (10 * 60, 11 * 60), (12 * 60 + 30, 15 * 60 + 30),
                     (16 * 60, 16 * 60 + 30)]
    }

    # Joyce's preference: not before 12:00 on Monday
    joyce_preference = {
        'Monday': (12 * 60, work_end)
    }

    # Iterate through each day to find a suitable time
    for day in days:
        # Get busy intervals for both participants
        busy_intervals = joshua_busy[day] + joyce_busy[day]
        busy_intervals.sort()  # Sort by start time

        # Determine the effective start time based on Joyce's preference
        day_start = work_start
        if day in joyce_preference:
            day_start = max(day_start, joyce_preference[day][0])

        # Merge overlapping or adjacent busy intervals
        merged = []
        for start, end in busy_intervals:
            if not merged:
                merged.append((start, end))
            else:
                last_start, last_end = merged[-1]
                if start <= last_end:
                    new_start = min(last_start, start)
                    new_end = max(last_end, end)
                    merged[-1] = (new_start, new_end)
                else:
                    merged.append((start, end))

        # Check the time before the first busy interval
        if len(merged) > 0:
            first_start, first_end = merged[0]
            if first_start - day_start >= meeting_duration:
                meeting_start = day_start
                meeting_end = meeting_start + meeting_duration
                # Verify it's within work hours and after Joyce's preference
                if meeting_end <= work_end and meeting_start >= day_start:
                    return day, f"{format_time(meeting_start)}:{format_time(meeting_end)}"

        # Check the time between busy intervals
        for i in range(1, len(merged)):
            prev_end = merged[i-1][1]
            curr_start = merged[i][0]
            if curr_start - prev_end >= meeting_duration:
                meeting_start = prev_end
                meeting_end = meeting_start + meeting_duration
                # Ensure it's within work hours and after Joyce's preference
                if meeting_end <= work_end and meeting_start >= day_start:
                    return day, f"{format_time(meeting_start)}:{format_time(meeting_end)}"

        # Check the time after the last busy interval
        if len(merged) > 0:
            last_start, last_end = merged[-1]
            if work_end - last_end >= meeting_duration:
                meeting_start = last_end
                meeting_end = meeting_start + meeting_duration
                # Ensure it's after Joyce's preference
                if meeting_start >= day_start:
                    return day, f"{format_time(meeting_start)}:{format_time(meeting_end)}"
        else:
            # No busy intervals, schedule anytime after preference
            meeting_start = day_start
            meeting_end = meeting_start + meeting_duration
            if meeting_end <= work_end:
                return day, f"{format_time(meeting_start)}:{format_time(meeting_end)}"

    return "No time found", ""

def format_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

day, time_range = find_meeting_time()
print(f"{day}: {time_range}")