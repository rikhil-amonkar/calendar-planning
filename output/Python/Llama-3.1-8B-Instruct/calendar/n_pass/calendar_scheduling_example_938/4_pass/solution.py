def find_meeting_time(eugene_schedule, eric_schedule, eric_preferred_days):
    # Find the end of each time block in Eugene's schedule
    eugene_time_blocks = []
    for start, end in eugene_schedule['Monday']:
        eugene_time_blocks.append((start, end))
    for start, end in eugene_schedule['Tuesday']:
        eugene_time_blocks.append((start, end))
    for start, end in eugene_schedule['Wednesday']:
        eugene_time_blocks.append((start, end))
    for start, end in eugene_schedule['Thursday']:
        eugene_time_blocks.append((start, end))
    for start, end in eugene_schedule['Friday']:
        eugene_time_blocks.append((start, end))

    # Find the end of each time block in Eric's schedule
    eric_time_blocks = []
    for start, end in eric_schedule['Monday']:
        eric_time_blocks.append((start, end))
    for start, end in eric_schedule['Tuesday']:
        eric_time_blocks.append((start, end))
    for start, end in eric_schedule['Wednesday']:
        eric_time_blocks.append((start, end))
    for start, end in eric_schedule['Thursday']:
        eric_time_blocks.append((start, end))
    for start, end in eric_schedule['Friday']:
        eric_time_blocks.append((start, end))

    # Sort the time blocks by start time
    eugene_time_blocks.sort(key=lambda x: x[0])
    eric_time_blocks.sort(key=lambda x: x[0])

    # Find the first time block that is not conflicting
    eugene_start = eugene_time_blocks[0][0]
    eric_start = eric_time_blocks[0][0]
    while eugene_start < eugene_time_blocks[-1][0] and eric_start < eric_time_blocks[-1][0]:
        if eugene_start == eugene_time_blocks[-1][0] or eric_start == eric_time_blocks[-1][0]:
            break
        if eugene_time_blocks[-1][1] < eric_time_blocks[-1][0]:
            eugene_start = eugene_time_blocks[-1][0]
            eric_start = eric_time_blocks[-1][0]
            eugene_time_blocks.pop()
            eric_time_blocks.pop()
        else:
            eugene_start = eugene_time_blocks[-1][0]
            eric_start = eric_time_blocks[-1][0]
            eugene_time_blocks.pop()
            eric_time_blocks.pop()

    # Find the end of the meeting
    meeting_start = max(eugene_start, eric_start)
    meeting_end = meeting_start + 0.5
    return meeting_start, meeting_end

# Define the schedules for Eugene and Eric
eugene_schedule = {
    'Monday': [(9, 9.5), (11, 11.5), (12, 12.5), (13, 15)],
    'Tuesday': [],
    'Wednesday': [(9, 9.5), (12, 14), (14, 16.5)],
    'Thursday': [(9, 10), (11, 12.5)],
    'Friday': [(10, 10.5), (12, 12.5), (13, 13.5)]
}

eric_schedule = {
    'Monday': [(9, 17)],
    'Tuesday': [(9, 17)],
    'Wednesday': [(9, 11.5), (12, 14), (14, 16.5)],
    'Thursday': [(9, 17)],
    'Friday': [(9, 11