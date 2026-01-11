import json
from datetime import datetime, timedelta

def time_to_str(t):
    return f"{t.hour}:{t.minute:02d}"

def main():
    # Given data
    start_location = "Fisherman's Wharf"
    start_time = datetime.strptime("9:00", "%H:%M")
    
    kenneth_location = "Nob Hill"
    kenneth_start = datetime.strptime("14:15", "%H:%M")
    kenneth_end = datetime.strptime("19:45", "%H:%M")
    
    travel_time = timedelta(minutes=11)
    min_meeting_duration = timedelta(minutes=90)
    
    # We start at Fisherman's Wharf at 9:00
    # We can leave early to arrive exactly when Kenneth starts
    # Earliest arrival at Nob Hill is start_time + travel_time = 9:11
    # But Kenneth is only there from 14:15, so we must wait until then if we arrive early.
    # To minimize waiting, leave Fisherman's Wharf at 14:04 to arrive at 14:15.
    
    # Calculate departure time to arrive exactly at kenneth_start
    depart_to_kenneth = kenneth_start - travel_time
    # If departure is earlier than current time, we can leave immediately (but here it's later)
    
    # Meeting with Kenneth
    meeting_start = kenneth_start
    meeting_end = meeting_start + min_meeting_duration
    
    # Ensure meeting doesn't exceed Kenneth's availability
    if meeting_end > kenneth_end:
        meeting_end = kenneth_end
        # But then meeting duration < 90 minutes, so not valid. Need to adjust start earlier.
        # Actually, since kenneth_end - kenneth_start = 5.5 hours > 90 min, it's fine.
    
    # Build itinerary
    itinerary = []
    
    # Travel to Nob Hill
    itinerary.append({
        "action": "travel",
        "location": "Fisherman's Wharf to Nob Hill",
        "person": "",
        "start_time": time_to_str(depart_to_kenneth),
        "end_time": time_to_str(kenneth_start)
    })
    
    # Meet Kenneth
    itinerary.append({
        "action": "meet",
        "location": kenneth_location,
        "person": "Kenneth",
        "start_time": time_to_str(meeting_start),
        "end_time": time_to_str(meeting_end)
    })
    
    # Travel back (optional, but included for completeness)
    travel_back_start = meeting_end
    travel_back_end = meeting_end + travel_time
    itinerary.append({
        "action": "travel",
        "location": "Nob Hill to Fisherman's Wharf",
        "person": "",
        "start_time": time_to_str(travel_back_start),
        "end_time": time_to_str(travel_back_end)
    })
    
    # Output as JSON
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()