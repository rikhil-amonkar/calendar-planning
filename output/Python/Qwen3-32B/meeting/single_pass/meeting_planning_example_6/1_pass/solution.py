import json

def minutes_to_time(m):
    hours = m // 60
    mins = m % 60
    return f"{hours}:{mins:02d}"

# Input parameters
start_location = "Fisherman's Wharf"
start_time = 9 * 60  # 9:00 AM in minutes
kenneth_start_time = 14 * 60 + 15  # 2:15 PM
kenneth_end_time = 19 * 60 + 45  # 7:45 PM
min_meeting_duration = 90  # minutes
travel_time_wharf_to_nob = 11  # minutes

# Calculate possible meeting with Kenneth
meeting_start = kenneth_start_time
meeting_end = meeting_start + min_meeting_duration

# Check if meeting fits in Kenneth's schedule
if meeting_end <= kenneth_end_time:
    # Calculate departure time from Fisherman's Wharf
    # Must arrive at Nob Hill by meeting_start, which is 2:15 PM
    departure_time = meeting_start - travel_time_wharf_to_nob
    # Since departure_time must be >= start_time (9:00 AM), which it is (844 >= 540)
    # So it's valid
    itinerary = [
        {
            "action": "meet",
            "location": "Nob Hill",
            "person": "Kenneth",
            "start_time": minutes_to_time(meeting_start),
            "end_time": minutes_to_time(meeting_end)
        }
    ]
else:
    # No meeting possible, but according to problem constraints it is
    itinerary = []

result = {"itinerary": itinerary}

print(json.dumps(result, indent=2))