from datetime import datetime, timedelta

# Define the meeting duration and the work hours
MEETING_DURATION = timedelta(minutes=30)
WORK_START = datetime.strptime("09:00", "%H:%M")
WORK_END = datetime.strptime("17:00", "%H:%M")

# Define the participants' schedules
schedules = {
    "Doris": [(WORK_START, WORK_START + timedelta(hours=2)), 
              (WORK_START + timedelta(hours=4), WORK_START + timedelta(hours=4, minutes=30))],
    "Theresa": [(WORK_START + timedelta(hours=1), WORK_START + timedelta(hours=3))],
    "Christian": [(WORK_START, WORK_END)],
    "Terry": [(WORK_START + timedelta(minutes=30), WORK_START + timedelta(hours=1)),
              (WORK_START + timedelta(hours=1, minutes=30), WORK_START + timedelta(hours=1, minutes=30)),
              (WORK_START + timedelta(hours=2, minutes=30), WORK_END)],
    "Carolyn": [(WORK_START, WORK_START + timedelta(hours=1, minutes=30)),
                (WORK_START + timedelta(hours=1), WORK_START + timedelta(hours=2)),
                (WORK_START + timedelta(hours=2, minutes=30), WORK_END)],
    "Kyle": [(WORK_START, WORK_START + timedelta(minutes=30)),
             (WORK_START + timedelta(hours=1, minutes=30), WORK_START + timedelta(hours=2)),
             (WORK_START + timedelta(hours=5), WORK_END)],
}

# Find free slots for all participants
def find_free_slots(schedules):
    all_free_slots = []
    for name, slots in schedules.items():
        free_slots = []
        current_start = WORK_START
        
        for start, end in sorted(slots):
            if current_start < start:
                free_slots.append((current_start, start))
            current_start = max(current_start, end)
        
        if current_start < WORK_END:
            free_slots.append((current_start, WORK_END))
        
        all_free_slots.append(free_slots)
    
    return all_free_slots

def find_common_slot(all_free_slots):
    common_slots = set(all_free_slots[0])  # Start with the first participant's slots
    for free_slots in all_free_slots[1:]:
        common_slots.intersection_update(set(free_slots))
    
    return list(common_slots)

free_slots = find_free_slots(schedules)
common_slots = find_common_slot(free_slots)

# Check for a suitable slot for the meeting
def get_meeting_time(common_slots):
    for start, end in common_slots:
        if end - start >= MEETING_DURATION:
            meeting_start = start
            meeting_end = meeting_start + MEETING_DURATION
            return meeting_start.strftime("%H:%M"), meeting_end.strftime("%H:%M")
    return None

meeting_time = get_meeting_time(common_slots)

# Output the result
if meeting_time:
    print(f"Time Range: {{{meeting_time[0]}:{meeting_time[1]}}}, Day: Monday")
else:
    print("No available time found for scheduling the meeting.")