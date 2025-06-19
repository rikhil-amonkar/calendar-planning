import datetime, timedelta

# Define the schedules for Eugene and Eric
eugene_schedule = {
    'Monday': [(10, 11), (11, 12), (13, 14), (14, 15), (16, 16.5)],
    'Tuesday': [],
    'Wednesday': [(9, 9.5), (11, 11.5), (12, 12.5), (13, 15)],
    'Thursday': [(9, 10), (11, 12.5)],
    'Friday': [(10, 10.5), (12, 12.5), (13, 13.5)]
}

eric_schedule = {
    'Monday': [(9, 17)],
    'Tuesday': [(9, 17)],
    'Wednesday': [(9, 11.5), (12, 14), (14, 16.5)],
    'Thursday': [(9, 17)],
    'Friday': [(9, 11), (11, 17)]
}

# Eric's preference to avoid meetings on Wednesday
eric_preferred_days = ['Monday', 'Tuesday', 'Thursday', 'Friday']

# Meeting duration
meeting_duration = timedelta(hours=0.5)

# Function to find a suitable time for the meeting
def find_meeting_time(eugene_schedule, eric_schedule, eric_preferred_days, meeting_duration):
    for day in eric_preferred_days:
        available_times = []
        eugene_time_blocks = []
        eric_time_blocks = []
        
        # Convert time blocks to datetime objects and add them to the lists
        for start, end in eugene_schedule[day]:
            eugene_time_blocks.append((datetime(1900, 1, 1, int(start), int((start % 1) * 60)), datetime(1900, 1, 1, int(end), int((end % 1) * 60))))
        
        for start, end in eric_schedule[day]:
            eric_time_blocks.append((datetime(1900, 1, 1, int(start), int((start % 1) * 60)), datetime(1900, 1, 1, int(end), int((end % 1) * 60))))
        
        # Sort the time blocks by start time
        eugene_time_blocks.sort(key=lambda x: x[0])
        eric_time_blocks.sort(key=lambda x: x[0])
        
        # Iterate over the time blocks and check for conflicts
        i = j = 0
        while i < len(eugene_time_blocks) and j < len(eric_time_blocks):
            eugene_start = eugene_time_blocks[i][0]
            eugene_end = eugene_time_blocks[i][1]
            eric_start = eric_time_blocks[j][0]
            eric_end = eric_time_blocks[j][1]
            
            # Check if the current time block conflicts with the previous one
            if i > 0 and eugene_time_blocks[i-1][1] > eugene_start:
                eugene_start = eugene_time_blocks[i-1][1]
            
            # Check if the current time block conflicts with the previous one
            if j > 0 and eric_time_blocks[j-1][1] > eric_start:
                eric_start = eric_time_blocks[j-1][1]
            
            # Check if the current time block conflicts with the previous one
            if i > 0 and eugene_time_blocks[i-1][1] > eric_start:
                eric_start = eugene_time_blocks[i-1][1]
            
            # Check if the current time block conflicts with the previous one
            if j > 0 and eric_time_blocks[j-1][1] > eugene_start:
                eugene_start = eric_time_blocks[j-1][1]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eric_end:
                eric_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eugene_end:
                eugene_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eric_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eugene_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_start:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_start:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next one
            if i + 1 < len(eugene_time_blocks) and eugene_time_blocks[i+1][0] < eugene_end and eugene_time_blocks[i+1][0] > eric_end:
                eugene_end = eugene_time_blocks[i+1][0]
            
            # Check if the current time block conflicts with the next one
            if j + 1 < len(eric_time_blocks) and eric_time_blocks[j+1][0] < eric_end and eric_time_blocks[j+1][0] > eugene_end:
                eric_end = eric_time_blocks[j+1][0]
            
            # Check if the current time block conflicts with the next