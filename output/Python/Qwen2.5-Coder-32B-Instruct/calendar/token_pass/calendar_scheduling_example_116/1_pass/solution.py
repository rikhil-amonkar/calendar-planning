# Define the work hours and meeting duration
work_start = 9 * 60  # Convert 9:00 AM to minutes since midnight
work_end = 17 * 60   # Convert 5:00 PM to minutes since midnight
meeting_duration = 30  # Meeting duration in minutes

# Busy times for each participant in minutes since midnight
adam_busy = [(14 * 60, 15 * 60)]  # 14:00 to 15:00
john_busy = [(13 * 60 + 30, 14 * 60), (14 * 60, 14 * 60 + 30), (15 * 60 + 30, 16 * 60), (16 * 60 + 30, 17 * 60)]
stephanie_busy = [(9 * 60 + 30, 10 * 60), (10 * 60 + 30, 11 * 60), (11 * 60 + 30, 16 * 60), (16 * 60 + 30, 17 * 60)]
anna_busy = [(9 * 60 + 30, 10 * 60), (12 * 60, 12 * 60 + 30), (13 * 60, 15 * 60 + 30), (16 * 60 + 30, 17 * 60), (9 * 60, 14 * 60 + 30)]  # Added preference

# Function to check if a time slot is free for all participants
def is_free_for_all(start_time, end_time):
    for busy_times in [adam_busy, john_busy, stephanie_busy, anna_busy]:
        for busy_start, busy_end in busy_times:
            if not (end_time <= busy_start or start_time >= busy_end):
                return False
    return True

# Iterate through possible meeting times
for start_time in range(work_start, work_end - meeting_duration + 1, 30):
    end_time = start_time + meeting_duration
    if is_free_for_all(start_time, end_time):
        # Convert back to HH:MM format
        start_hour = start_time // 60
        start_minute = start_time % 60
        end_hour = end_time // 60
        end_minute = end_time % 60
        print(f"{start_hour:02}:{start_minute:02}:{end_hour:02}:{end_minute:02} Monday")
        break