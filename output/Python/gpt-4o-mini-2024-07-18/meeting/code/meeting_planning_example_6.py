import json
from datetime import datetime, timedelta

# Input parameters
arrival_time = datetime.strptime("9:00", "%H:%M")
travel_time_wharf_to_nobhill = timedelta(minutes=11)
travel_time_nobhill_to_wharf = timedelta(minutes=11)
ken_start_time = datetime.strptime("14:15", "%H:%M")
ken_end_time = datetime.strptime("19:45", "%H:%M")
min_meeting_duration = timedelta(minutes=90)

# Calculate available meeting windows
def compute_meeting_schedule():
    itinerary = []
    current_time = arrival_time
    
    # Check if we can meet Kenneth after arriving at Fisherman's Wharf
    if ken_start_time - travel_time_nobhill_to_wharf >= current_time:
        # Calculate when we can meet Kenneth considering the minimum duration
        meeting_start = max(ken_start_time - min_meeting_duration, current_time + travel_time_wharf_to_nobhill)
        
        # Ensure the meeting cannot exceed Kenneth's availability
        meeting_end = min(meeting_start + min_meeting_duration, ken_end_time)

        if meeting_end > meeting_start:  # Valid meeting time found
            itinerary.append({
                "action": "meet",
                "location": "Nob Hill",
                "person": "Kenneth",
                "start_time": meeting_start.strftime("%H:%M"),
                "end_time": meeting_end.strftime("%H:%M")
            })
            current_time = meeting_end  # Update current time after meeting

    # Consider meeting other friends; assume they can meet after Kenneth
    # For simplicity, we assume 1 hour meeting with another friend nearby
    if current_time + travel_time_nobhill_to_wharf <= ken_end_time:  # Still time for another meeting
        other_meeting_start = current_time + travel_time_nobhill_to_wharf
        other_meeting_end = other_meeting_start + timedelta(hours=1)
        
        if other_meeting_end <= ken_end_time:  # Ensure it fits into Kenneth's availability
            itinerary.append({
                "action": "meet",
                "location": "Fisherman's Wharf",
                "person": "Friend",
                "start_time": other_meeting_start.strftime("%H:%M"),
                "end_time": other_meeting_end.strftime("%H:%M")
            })

    return {
        "itinerary": itinerary
    }

# Compute the meeting schedule
schedule = compute_meeting_schedule()

# Output result as JSON
print(json.dumps(schedule, indent=2))