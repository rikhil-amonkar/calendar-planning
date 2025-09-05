import json

def minutes_to_time_str(total_minutes):
    hours = total_minutes // 60
    minutes = total_minutes % 60
    return f"{hours}:{minutes:02d}"

# Input parameters in minutes since midnight
arrival_fisher = 9 * 60  # 9:00 AM -> 540
travel_fisher_to_nob = 11  # minutes from Fisherman's Wharf to Nob Hill
travel_nob_to_fisher = 11  # minutes from Nob Hill to Fisherman's Wharf

# Kenneth's availability at Nob Hill: 14:15 to 19:45
kenneth_start = 14 * 60 + 15  # 14:15 -> 855
kenneth_end = 19 * 60 + 45    # 19:45 -> 1185

min_meeting_duration = 90  # in minutes

# Compute the optimal departure time from Fisherman's Wharf so that you arrive at Nob Hill 
# exactly when Kenneth becomes available.
departure_time = kenneth_start - travel_fisher_to_nob

if departure_time < arrival_fisher:
    raise ValueError("Departure time is before arrival time. Check your constraints.")

# Since you want to maximize friend time during your visit,
# you should minimize idle time. Thus, you wait at Fisherman's Wharf until the optimal departure time,
# travel for 11 minutes, and start your meeting with Kenneth exactly at his arrival.
meeting_start = kenneth_start

# The available meeting window with Kenneth
available_duration = kenneth_end - meeting_start
if available_duration < min_meeting_duration:
    raise ValueError("Not enough time to meet Kenneth for the required duration.")

# For an optimal schedule (maximizing friend interactions during your visit),
# meet Kenneth for the entire duration he is available.
meeting_end = kenneth_end

# Build the itinerary.
# Although travel time is accounted for in the scheduling calculations,
# the itinerary output focuses on meeting actions.
itinerary = [
    {
        "action": "meet",
        "location": "Nob Hill",
        "person": "Kenneth",
        "start_time": minutes_to_time_str(meeting_start),
        "end_time": minutes_to_time_str(meeting_end)
    }
]

schedule = {"itinerary": itinerary}

# Output the resulting schedule as JSON-formatted dictionary.
print(json.dumps(schedule, indent=2))