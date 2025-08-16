from datetime import datetime, timedelta

def find_meeting_time(kayla_blocks, rebecca_blocks, meeting_duration, work_start, work_end, day_of_week):
    # Convert times to datetime objects
    work_start_dt = datetime.strptime(work_start, "%H:%M")
    work_end_dt = datetime.strptime(work_end, "%H:%M")
    
    # Function to convert string time to datetime object
    def str_to_time(time_str):
        return datetime.strptime(time_str, "%H:%M")
    
    # Convert all block times to datetime objects
    kayla_blocks_dt = [(str_to_time(start), str_to_time(end)) for start, end in kayla_blocks]
    rebecca_blocks_dt = [(str_to_time(start), str_to_time(end)) for start, end in rebecca_blocks]
    
    # Combine all blocks
    all_blocks = sorted(kayla_blocks_dt + rebecca_blocks_dt)
    
    # Initialize variables to track potential meeting slots
    current_start = work_start_dt
    
    for block_start, block_end in all_blocks:
        # Check if there's a gap between the current start and the next block
        if block_start > current_start:
            potential_meeting_start = current_start
            potential_meeting_end = potential_meeting_start + timedelta(hours=meeting_duration)
            
            # Check if the potential meeting fits within the workday and doesn't overlap with any blocks
            if potential_meeting_end <= block_start and potential_meeting_end <= work_end_dt:
                # Found a valid meeting time
                return f"{potential_meeting_start.strftime('%H:%M')}:{potential_meeting_end.strftime('%H:%M')}", day_of_week
        
        # Move the current start to the end of the current block
        current_start = max(current_start, block_end)
    
    # Check if there's a slot after the last block
    if work_end_dt - current_start >= timedelta(hours=meeting_duration):
        meeting_start = current_start
        meeting_end = meeting_start + timedelta(hours=meeting_duration)
        return f"{meeting_start.strftime('%H:%M')}:{meeting_end.strftime('%H:%M')}", day_of_week
    
    return None, None

# Define the constraints
kayla_blocks = [("10:00", "10:30"), ("14:30", "16:00")]
rebecca_blocks = [("9:00", "13:00"), ("13:30", "15:00"), ("15:30", "16:00")]
meeting_duration = 1  # in hours
work_start = "9:00"
work_end = "17:00"
day_of_week = "Monday"

# Find the meeting time
meeting_time, meeting_day = find_meeting_time(kayla_blocks, rebecca_blocks, meeting_duration, work_start, work_end, day_of_week)

# Output the result
print(f"{meeting_time}, {meeting_day}")