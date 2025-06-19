import json

def time_to_minutes(time_str):
    parts = time_str.split(':')
    hours = int(parts[0])
    minutes = int(parts[1])
    return hours * 60 + minutes

def minutes_to_time(minutes_val):
    hours = minutes_val // 60
    minutes_remainder = minutes_val % 60
    return f"{hours}:{minutes_remainder:02d}"

start_time_at_park = "9:00"
david_available_start = "16:00"
david_available_end = "21:45"
min_meeting_duration = 105
travel_time = 23

start_min = time_to_minutes(start_time_at_park)
david_start_min = time_to_minutes(david_available_start)
david_end_min = time_to_minutes(david_available_end)

meeting_start_min = david_start_min
meeting_end_min = meeting_start_min + min_meeting_duration

if meeting_end_min > david_end_min:
    meeting_start_min = david_end_min - min_meeting_duration
    meeting_end_min = david_end_min

leave_min = meeting_start_min - travel_time
if leave_min < start_min:
    arrival_min = start_min + travel_time
    meeting_start_min = max(arrival_min, david_start_min)
    meeting_end_min = meeting_start_min + min_meeting_duration
    if meeting_end_min > david_end_min:
        meeting_end_min = david_end_min

meeting_duration = meeting_end_min - meeting_start_min
if meeting_duration >= min_meeting_duration:
    itinerary = [
        {
            "action": "meet",
            "location": "Chinatown",
            "person": "David",
            "start_time": minutes_to_time(meeting_start_min),
            "end_time": minutes_to_time(meeting_end_min)
        }
    ]
else:
    itinerary = []

result = {"itinerary": itinerary}
print(json.dumps(result, indent=2))