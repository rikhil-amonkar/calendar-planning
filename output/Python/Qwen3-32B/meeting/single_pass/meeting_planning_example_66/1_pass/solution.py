import json

def to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def to_time_str(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Input parameters
user_start_location = "Nob Hill"
user_start_time = "9:00"
robert_location = "Presidio"
robert_name = "Robert"
robert_start_time = "11:15"
robert_end_time = "17:45"
required_meeting_duration = 120
travel_nob_to_pres = 17
travel_pres_to_nob = 18  # Not used in this scenario

# Calculate earliest arrival at Presidio
user_start_minutes = to_minutes(user_start_time)
earliest_arrival_pres = user_start_minutes + travel_nob_to_pres

# Robert's available times in minutes
robert_start_minutes = to_minutes(robert_start_time)
robert_end_minutes = to_minutes(robert_end_time)

# Determine meeting start time
meeting_start_minutes = max(earliest_arrival_pres, robert_start_minutes)

# Check if meeting can fit
meeting_end_minutes = meeting_start_minutes + required_meeting_duration
if meeting_end_minutes <= robert_end_minutes:
    meeting_start_time = to_time_str(meeting_start_minutes)
    meeting_end_time = to_time_str(meeting_end_minutes)
    itinerary = [
        {
            "action": "meet",
            "location": robert_location,
            "person": robert_name,
            "start_time": meeting_start_time,
            "end_time": meeting_end_time
        }
    ]
    print(json.dumps({"itinerary": itinerary}))
else:
    print(json.dumps({"itinerary": []}))