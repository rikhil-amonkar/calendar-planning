import json

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Input Parameters

# Arrival time at Richmond District (in minutes since midnight)
arrival_richmond = 9 * 60  # 9:00 AM -> 540 minutes

# Travel times in minutes between districts
travel_times = {
    ("Richmond District", "Pacific Heights"): 10,
    ("Richmond District", "Marina District"): 9,
    ("Pacific Heights", "Richmond District"): 12,
    ("Pacific Heights", "Marina District"): 6,
    ("Marina District", "Richmond District"): 11,
    ("Marina District", "Pacific Heights"): 7
}

# Friend meeting constraints (times in minutes since midnight)
# Carol: Available at Marina District from 11:30 (690) to 15:00 (900), minimum meeting 60 minutes.
carol_available_start = 11 * 60 + 30  # 690
carol_available_end = 15 * 60           # 900
carol_min_duration = 60

# Jessica: Available at Pacific Heights from 15:30 (930) to 16:45 (1005), minimum meeting 45 minutes.
jessica_available_start = 15 * 60 + 30  # 930
jessica_available_end = 16 * 60 + 45     # 1005
jessica_min_duration = 45

# We want to maximize the number of friends met.
# Since the available windows do not overlap, the meeting order must be:
# 1. Meet Carol at Marina District
# 2. Meet Jessica at Pacific Heights

# To minimize idle waiting at the meeting locations, we choose to schedule Carol's meeting as late as possible.
# The latest Carol can start her meeting is constrained by her available end and the minimum duration.
latest_possible_carol_start = carol_available_end - carol_min_duration  # 900 - 60 = 840 (14:00)

# Compute the departure time from Richmond District needed to arrive just in time at Marina District
# Travel time from Richmond District to Marina District is 9 minutes.
departure_from_richmond = latest_possible_carol_start - travel_times[("Richmond District", "Marina District")]
# Ensure we don't leave before arriving at Richmond
if departure_from_richmond < arrival_richmond:
    departure_from_richmond = arrival_richmond

# Carol meeting is scheduled at Marina District
carol_meeting_start = latest_possible_carol_start           # 840 minutes -> 14:00
carol_meeting_end = carol_meeting_start + carol_min_duration   # 840 + 60 = 900 minutes -> 15:00

# After meeting Carol, travel from Marina District to Pacific Heights takes 7 minutes.
arrival_at_pacific = carol_meeting_end + travel_times[("Marina District", "Pacific Heights")]  # 900 + 7 = 907 minutes

# Jessica's meeting can start as soon as she is available and after arrival.
jessica_meeting_start = max(jessica_available_start, arrival_at_pacific)  # max(930, 907) = 930 minutes -> 15:30
jessica_meeting_end = jessica_meeting_start + jessica_min_duration         # 930 + 45 = 975 minutes -> 16:15

# Build the itinerary output in the required JSON structure.
itinerary = [
    {
        "action": "meet",
        "location": "Marina District",
        "person": "Carol",
        "start_time": minutes_to_time(carol_meeting_start),
        "end_time": minutes_to_time(carol_meeting_end)
    },
    {
        "action": "meet",
        "location": "Pacific Heights",
        "person": "Jessica",
        "start_time": minutes_to_time(jessica_meeting_start),
        "end_time": minutes_to_time(jessica_meeting_end)
    }
]

schedule = {"itinerary": itinerary}

# Output the resulting schedule as a JSON-formatted dictionary.
print(json.dumps(schedule))