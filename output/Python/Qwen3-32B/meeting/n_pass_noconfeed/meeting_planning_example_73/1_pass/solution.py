import json

def time_to_minutes(t):
    h, m = map(int, t.split(':'))
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    min = m % 60
    return f"{h}:{min:02d}"

# Input parameters
user_start_russian_hill = "9:00"
barbara_available_start = "7:15"
barbara_available_end = "22:00"
min_meeting_duration = 60
travel_time_russian_to_pacific = 7  # minutes

# Calculations
user_start_min = time_to_minutes(user_start_russian_hill)
arrival_pacific = user_start_min + travel_time_russian_to_pacific

barbara_end_min = time_to_minutes(barbara_available_end)
latest_start = barbara_end_min - min_meeting_duration

if arrival_pacific <= latest_start:
    meeting_start = arrival_pacific
    meeting_end = meeting_start + min_meeting_duration
else:
    # No feasible meeting time (should not occur with given constraints)
    raise ValueError("No possible meeting time with given constraints")

# Convert to time strings
start_time_str = minutes_to_time(meeting_start)
end_time_str = minutes_to_time(meeting_end)

itinerary = [
    {
        "action": "meet",
        "location": "Pacific Heights",
        "person": "Barbara",
        "start_time": start_time_str,
        "end_time": end_time_str
    }
]

result = {"itinerary": itinerary}

print(json.dumps(result, indent=2))