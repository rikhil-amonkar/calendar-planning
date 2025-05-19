#!/usr/bin/env python3
import json
from datetime import datetime, timedelta

# Helper function to format time without leading zeros in hour
def format_time(dt):
    return f"{dt.hour}:{dt.minute:02d}"

# Input parameters and travel times (all in minutes)
start_location = "Richmond District"
arrival_time = datetime(2023, 1, 1, 9, 0)  # 9:00 AM

# Meeting constraints
# Carol: at Marina District, available 11:30 to 15:00, need minimum 60 minutes
carol_location = "Marina District"
carol_avail_start = datetime(2023, 1, 1, 11, 30)
carol_avail_end   = datetime(2023, 1, 1, 15, 0)
min_carol_meeting = timedelta(minutes=60)

# Jessica: at Pacific Heights, available 15:30 to 16:45, need minimum 45 minutes
jessica_location = "Pacific Heights"
jessica_avail_start = datetime(2023, 1, 1, 15, 30)
jessica_avail_end   = datetime(2023, 1, 1, 16, 45)
min_jessica_meeting = timedelta(minutes=45)

# Travel times dictionary: (from, to) : travel time in minutes
travel_times = {
    ("Richmond District", "Pacific Heights"): 10,
    ("Richmond District", "Marina District"): 9,
    ("Pacific Heights", "Richmond District"): 12,
    ("Pacific Heights", "Marina District"): 6,
    ("Marina District", "Richmond District"): 11,
    ("Marina District", "Pacific Heights"): 7
}

# We want to meet as many friends as possible, so we plan to meet Carol and Jessica.
# The only feasible order is:
# 1. Start from Richmond District at 9:00, travel to Marina District (for Carol).
# 2. Wait until Carol's availability window begins (11:30), meet Carol for at least 60 minutes.
# 3. After finishing with Carol, travel to Pacific Heights for Jessica.
# 4. Wait until Jessica is available (15:30) and meet her for at least 45 minutes.
# We now compute each of these steps.

# Step 1: Travel from Richmond District (start) to Marina District for Carol.
travel_time_to_carol = timedelta(minutes=travel_times[(start_location, carol_location)])
arrival_at_carol = arrival_time + travel_time_to_carol
# If we arrive before Carol is available, we wait until her availability starts.
meeting_carol_start = max(arrival_at_carol, carol_avail_start)
# Meeting Carol for the minimum required duration.
meeting_carol_end = meeting_carol_start + min_carol_meeting

# Step 2: Travel from Marina District (Carol's location) to Pacific Heights (Jessica's location)
travel_time_to_jessica = timedelta(minutes=travel_times[(carol_location, jessica_location)])
arrival_at_jessica = meeting_carol_end + travel_time_to_jessica
# Wait until Jessica's availability starts, if needed.
meeting_jessica_start = max(arrival_at_jessica, jessica_avail_start)
meeting_jessica_end = meeting_jessica_start + min_jessica_meeting
# Ensure we do not exceed Jessica's availability window.
if meeting_jessica_end > jessica_avail_end:
    # Adjust meeting end if necessary (though in our computed schedule it won't happen)
    meeting_jessica_end = jessica_avail_end

# Build the itinerary output as a JSON object.
itinerary = [
    {
        "action": "meet",
        "location": carol_location,
        "person": "Carol",
        "start_time": format_time(meeting_carol_start),
        "end_time": format_time(meeting_carol_end)
    },
    {
        "action": "meet",
        "location": jessica_location,
        "person": "Jessica",
        "start_time": format_time(meeting_jessica_start),
        "end_time": format_time(meeting_jessica_end)
    }
]

output = {
    "itinerary": itinerary
}

# Print the JSON-formatted schedule
print(json.dumps(output, indent=2))