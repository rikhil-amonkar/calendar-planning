import json

def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Input parameters
arrival_time = "9:00"
david_available_start = "16:00"
david_available_end = "21:45"
meeting_duration = 105
travel_time_park_to_chinatown = 23
travel_time_chinatown_to_park = 23

# Convert times to minutes
current_time = time_to_minutes(arrival_time)
david_start = time_to_minutes(david_available_start)
david_end = time_to_minutes(david_available_end)

# Calculate latest possible departure from Golden Gate Park to meet David
latest_departure_to_meet_david = david_end - meeting_duration - travel_time_park_to_chinatown

# Calculate possible meeting time with David
if latest_departure_to_meet_david >= current_time + travel_time_park_to_chinatown:
    # We can go directly to meet David
    meet_start = max(david_start, current_time + travel_time_park_to_chinatown)
    meet_end = meet_start + meeting_duration
    if meet_end <= david_end:
        itinerary = [
            {
                "action": "travel",
                "location": "Golden Gate Park to Chinatown",
                "person": "You",
                "start_time": minutes_to_time(current_time),
                "end_time": minutes_to_time(current_time + travel_time_park_to_chinatown)
            },
            {
                "action": "meet",
                "location": "Chinatown",
                "person": "David",
                "start_time": minutes_to_time(meet_start),
                "end_time": minutes_to_time(meet_end)
            }
        ]
    else:
        itinerary = []
else:
    itinerary = []

result = {
    "itinerary": itinerary
}

print(json.dumps(result, indent=2))