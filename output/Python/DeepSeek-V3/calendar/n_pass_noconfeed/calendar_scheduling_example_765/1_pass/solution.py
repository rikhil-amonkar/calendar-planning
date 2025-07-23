def find_meeting_time():
    # Define work hours and days to consider
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60    # 17:00 in minutes
    days = ['Monday', 'Tuesday', 'Wednesday']
    meeting_duration = 30  # minutes

    # Define busy times for each participant in minutes since midnight
    # Format: {day: [(start1, end1), (start2, end2), ...]}
    joshua_busy = {
        'Monday': [(15 * 60, 15 * 60 + 30)],
        'Tuesday': [(11 * 60 + 30, 12 * 60), (13 * 60, 13 * 60 + 30), (14 * 60 + 30, 15 * 60)],
        'Wednesday': []
    }
    
    joyce_busy = {
        'Monday': [(9 * 60, 9 * 60 + 30), (10 * 60, 11 * 60), (11 * 60 + 30, 12 * 60 + 30),
                   (13 * 60, 15 * 60), (15 * 60 + 30, 17 * 60)],
        'Tuesday': [(9 * 60, 17 * 60)],
        'Wednesday': [(9 * 60, 9 * 60 + 30), (10 * 60, 11 * 60), (12 * 60 + 30, 15 * 60 + 30),
                      (16 * 60, 16 * 60 + 30)]
    }

    # Joyce's preference: not before 12:00 on Monday
    joyce_preference = {
        'Monday': 12 * 60  # 12:00 in minutes
    }

    # Iterate through each day to find a suitable time
    for day in days:
        # Combine and sort all busy intervals for both participants
        all_busy = joshua_busy.get(day, []) + joyce_busy.get(day, [])
        all_busy.sort()

        # Initialize the previous end time to work start
        prev_end = work_start

        # Check Joyce's preference for Monday
        if day == 'Monday':
            prev_end = max(prev_end, joyce_preference['Monday'])

        # Iterate through busy intervals to find a gap
        for start, end in all_busy:
            if start > prev_end and start - prev_end >= meeting_duration:
                # Found a suitable gap
                meeting_start = prev_end
                meeting_end = meeting_start + meeting_duration
                return day, meeting_start, meeting_end
            prev_end = max(prev_end, end)

        # Check the gap after the last busy interval
        if work_end - prev_end >= meeting_duration:
            meeting_start = prev_end
            meeting_end = meeting_start + meeting_duration
            return day, meeting_start, meeting_end

    return None  # No suitable time found (though per problem statement, one exists)

# Run the function and format the output
day, start, end = find_meeting_time()
start_hr = start // 60
start_min = start % 60
end_hr = end // 60
end_min = end % 60

print(f"{day}: {{{start_hr:02d}:{start_min:02d}:{end_hr:02d}:{end_min:02d}}}")