import json

def minutes_to_time(m):
    hours = m // 60
    mins = m % 60
    return f"{hours}:{mins:02d}"

# Input parameters
arrival_russian_hill = 9 * 60 + 0  # 9:00 AM in minutes
barbara_start = 13 * 60 + 15       # 1:15 PM
barbara_end = 18 * 60 + 15         # 6:15 PM
min_meeting = 45
travel_russian_to_richmond = 14

# Calculate departure time from Russian Hill
departure_russian = barbara_start - travel_russian_to_richmond

# Check if departure is possible (after arrival at Russian Hill)
if departure_russian >= arrival_russian_hill:
    # Calculate meeting end time
    meeting_start = barbara_start
    meeting_end = meeting_start + min_meeting
    if meeting_end <= barbara_end:
        # Create itinerary
        itinerary = [
            {
                "action": "meet",
                "location": "Richmond District",
                "person": "Barbara",
                "start_time": minutes_to_time(meeting_start),
                "end_time": minutes_to_time(meeting_end)
            }
        ]
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        # Meeting would end after Barbara leaves. Not possible.
        print(json.dumps({"itinerary": []}))
else:
    # Cannot leave Russian Hill in time. No meeting.
    print(json.dumps({"itinerary": []}))