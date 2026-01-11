from datetime import datetime, timedelta

# Define the busy times for each participant
busy_times = {
    "Christine": [(9, 30), (12, 0), (13, 0), (14, 30), (16, 0)],
    "Janice": [],
    "Bobby": [(12, 0), (14, 30)],
    "Elizabeth": [(9, 0), (11, 30), (13, 30), (15, 0), (16, 0)],
    "Tyler": [(9, 0), (12, 0), (13, 0), (15, 30), (16, 30)],
    "Edward": [(9, 0), (10, 0), (11, 30), (14, 30), (16, 0)]
}

# Define the duration of the meeting in minutes
meeting_duration = 30

# Define the workday start and end times
work_start = (9, 0)
work_end = (17, 0)

# Convert time tuples to datetime objects for easier manipulation
def time_to_datetime(time_tuple):
    return datetime(2023, 10, 1, time_tuple[0], time_tuple[1])

# Function to find free slots for a participant
def find_free_slots(busy_list, work_start, work_end):
    free_slots = []
    current_time = time_to_datetime(work_start)
    work_end_dt = time_to_datetime(work_end)
    
    for busy_start, busy_end in busy_list:
        busy_start_dt = time_to_datetime(busy_start)
        busy_end_dt = time_to_datetime(busy_end)
        
        if current_time < busy_start_dt:
            free_slots.append((current_time.time(), busy_start_dt.time()))
        
        current_time = max(current_time, busy_end_dt)
    
    if current_time < work_end_dt:
        free_slots.append((current_time.time(), work_end_dt.time()))
    
    return free_slots

# Function to convert time to minutes since start of the day
def time_to_minutes(t):
    return t.hour * 60 + t.minute

# Find free slots for all participants
free_slots_all = {name: find_free_slots(busy_times[name], work_start, work_end) for name in busy_times}

# Find overlapping free slots
common_free_slots = []

for start, end in free_slots_all["Christine"]:
    start_minutes = time_to_minutes(start)
    end_minutes = time_to_minutes(end)
    
    if end_minutes - start_minutes >= meeting_duration:
        valid_for_all = True
        
        for name in free_slots_all:
            if name == "Christine":
                continue
            
            participant_valid = False
            for p_start, p_end in free_slots_all[name]:
                p_start_minutes = time_to_minutes(p_start)
                p_end_minutes = time_to_minutes(p_end)
                
                if p_start_minutes <= start_minutes and p_end_minutes >= end_minutes:
                    participant_valid = True
                    break
            
            if not participant_valid:
                valid_for_all = False
                break
        
        if valid_for_all:
            common_free_slots.append((start, end))

# Apply Janice's preference
final_slot = None
for slot in common_free_slots:
    start, end = slot
    if start.hour < 13:
        final_slot = slot
        break

# Output the result
if final_slot:
    start_time_str = final_slot[0].strftime("%H:%M")
    end_time_str = final_slot[1].strftime("%H:%M")
    print(f"{start_time_str}:{end_time_str} Monday")
else:
    print("No suitable time slot found.")