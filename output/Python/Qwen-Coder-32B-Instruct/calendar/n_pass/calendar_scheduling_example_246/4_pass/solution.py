from datetime import datetime, timedelta

def find_meeting_time(participants, meeting_duration, start_time, end_time):
    # Convert start and end times to datetime objects
    start = datetime.strptime(start_time, "%H:%M")
    end = datetime.strptime(end_time, "%H:%M")
    
    # Initialize available slots for all participants
    available_slots = {name: [] for name in participants}
    
    # Populate available slots for each participant
    for name, schedule in participants.items():
        current = start
        for busy_start, busy_end in schedule:
            busy_start_dt = datetime.strptime(busy_start, "%H:%M")
            busy_end_dt = datetime.strptime(busy_end, "%H:%M")
            
            if current < busy_start_dt:
                available_slots[name].append((current, busy_start_dt))
            
            current = max(current, busy_end_dt)
        
        if current < end:
            available_slots[name].append((current, end))
    
    # Find common available slots
    common_slots = []
    for slot in available_slots[list(available_slots.keys())[0]]:
        start_slot, end_slot = slot
        duration = end_slot - start_slot
        
        if duration == timedelta(minutes=meeting_duration):
            is_common = True
            for other_slots in available_slots.values():
                found_exact_overlap = False
                for other_start, other_end in other_slots:
                    if start_slot < other_end and end_slot > other_start:
                        overlap_start = max(start_slot, other_start)
                        overlap_end = min(end_slot, other_end)
                        if (overlap_end - overlap_start) == timedelta(minutes=meeting_duration):
                            found_exact_overlap = True
                            break
                if not found_exact_overlap:
                    is_common = False
                    break
            
            if is_common:
                common_slots.append(slot)
    
    # Return the first common slot found
    if common_slots:
        common_start, common_end = common_slots[0]
        return common_start.strftime('%H:%M'), common_end.strftime('%H:%M')
    else:
        return None, None

# Participants' schedules
participants = {
    "Jacob": [("13:30", "14:00"), ("14:30", "15:00")],
    "Diana": [("09:30", "10:00"), ("11:30", "12:00"), ("13:00", "13:30"), ("16:00", "16:30")],
    "Adam": [("09:30", "10:30"), ("11:00", "12:30"), ("15:30", "16:00")],
    "Angela": [("09:30", "10:00"), ("10:30", "12:00"), ("13:00", "15:30"), ("16:00", "16:30")],
    "Dennis": [("09:00", "09:30"), ("10:30", "11:30"), ("13:00", "15:00"), ("16:30", "17:00")]
}

meeting_duration = 30  # in minutes
start_time = "09:00"
end_time = "17:00"

meeting_start, meeting_end = find_meeting_time(participants, meeting_duration, start_time, end_time)
print(f"{meeting_start}-{meeting_end} Monday" if meeting_start and meeting_end else "No common time slot found")