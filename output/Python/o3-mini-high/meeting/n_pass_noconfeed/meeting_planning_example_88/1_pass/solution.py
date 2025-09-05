import json

def minutes_to_time(minutes):
    # Convert minutes since midnight to a string in H:MM 24-hour format (no leading zero for the hour)
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Input parameters based on the problem statement
arrival_sunset = 9 * 60  # 9:00 AM in minutes (9*60 = 540)
joshua_available_start = 20 * 60 + 45   # 20:45 in minutes (20*60+45 = 1245)
joshua_available_end   = 21 * 60 + 45     # 21:45 in minutes (21*60+45 = 1305)
min_meeting_duration = 15  # in minutes

# Travel times (in minutes)
travel_sunset_to_gg = 11   # Sunset District to Golden Gate Park
travel_gg_to_sunset = 10   # Golden Gate Park to Sunset District

# Compute the departure time from Sunset District so as to arrive exactly when Joshua becomes available.
# We want to leave as late as possible to maximize our free time earlier in the day.
departure_from_sunset = joshua_available_start - travel_sunset_to_gg  # 1245 - 11 = 1234 minutes (20:34)
arrival_at_gg = departure_from_sunset + travel_sunset_to_gg           # should equal 1245 (20:45)

# Determine the meeting schedule with Joshua.
# To optimize the day (so as to be available for additional meetings later),
# we schedule the minimum required meeting duration.
meeting_start = max(joshua_available_start, arrival_at_gg)  # meeting starts when Joshua is available (20:45)
meeting_end = meeting_start + min_meeting_duration          # meeting lasts at least 15 minutes (ends at 21:00)

# Ensure the meeting does not extend past Joshua's available window.
if meeting_end > joshua_available_end:
    meeting_end = joshua_available_end

# Prepare the itinerary. In this case we only have one meeting event.
# (The schedule accounts for travel implicitly via the computed arrival time at Golden Gate Park.)
itinerary = [
    {
        "action": "meet",
        "location": "Golden Gate Park",
        "person": "Joshua",
        "start_time": minutes_to_time(meeting_start),
        "end_time": minutes_to_time(meeting_end)
    }
]

# Output the result as a JSON-formatted dictionary.
schedule = {"itinerary": itinerary}
print(json.dumps(schedule, indent=2))