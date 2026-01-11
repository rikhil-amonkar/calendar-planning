# Define the availability of Margaret and Alexis
margaret_availability = {
    'Monday': [(9, 10.5), (11, 11.5), (12, 13), (13.5, 15)],
    'Tuesday': [(9, 12), (12.5, 14), (14.5, 17)]
}

alexis_availability = {
    'Monday': [(9, 9.5), (11.5, 12.5), (13, 14), (14, 17)],
    'Tuesday': [(10.5, 14), (16.5, 17)]
}

# Meeting duration in hours
meeting_duration = 0.5

# Function to find common free time slots
def find_common_free_slots(margaret_slots, alexis_slots, start_time, end_time):
    common_slots = []
    i, j = 0, 0
    
    while i < len(margaret_slots) and j < len(alexis_slots):
        margaret_start, margaret_end = margaret_slots[i]
        alexis_start, alexis_end = alexis_slots[j]
        
        # Find the overlap
        overlap_start = max(margaret_start, alexis_start)
        overlap_end = min(margaret_end, alexis_end)
        
        if overlap_end - overlap_start >= meeting_duration:
            common_slots.append((overlap_start, overlap_start + meeting_duration))
        
        # Move to the next slot
        if margaret_end <= alexis_end:
            i += 1
        else:
            j += 1
    
    # Filter slots that end before the specified end time
    filtered_slots = [(start, end) for start, end in common_slots if end <= end_time]
    
    return filtered_slots

# Find common free slots on Tuesday before 14:30
common_slots_tuesday = find_common_free_slots(
    margaret_availability['Tuesday'],
    alexis_availability['Tuesday'],
    12, 14.5  # 12:00 to 14:30
)

# Convert the time to HH:MM format
def convert_to_hhmm(time_decimal):
    hours = int(time_decimal)
    minutes = int((time_decimal - hours) * 60)
    return f"{hours:02}:{minutes:02}"

# Output the first valid slot
if common_slots_tuesday:
    start, end = common_slots_tuesday[0]
    start_time = convert_to_hhmm(start)
    end_time = convert_to_hhmm(end)
    print(f"{start_time}:{end_time} Tuesday")
else:
    print("No valid slot found")