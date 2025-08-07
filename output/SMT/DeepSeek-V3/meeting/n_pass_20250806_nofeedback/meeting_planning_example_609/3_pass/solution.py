from z3 import *
import json

# Define the travel times between locations
travel_times = {
    ("Chinatown", "Mission District"): 18,
    ("Chinatown", "Alamo Square"): 17,
    ("Chinatown", "Pacific Heights"): 10,
    ("Chinatown", "Union Square"): 7,
    ("Chinatown", "Golden Gate Park"): 23,
    ("Chinatown", "Sunset District"): 29,
    ("Chinatown", "Presidio"): 19,
    ("Mission District", "Chinatown"): 16,
    ("Mission District", "Alamo Square"): 11,
    ("Mission District", "Pacific Heights"): 16,
    ("Mission District", "Union Square"): 15,
    ("Mission District", "Golden Gate Park"): 17,
    ("Mission District", "Sunset District"): 24,
    ("Mission District", "Presidio"): 25,
    ("Alamo Square", "Chinatown"): 16,
    ("Alamo Square", "Mission District"): 10,
    ("Alamo Square", "Pacific Heights"): 10,
    ("Alamo Square", "Union Square"): 14,
    ("Alamo Square", "Golden Gate Park"): 9,
    ("Alamo Square", "Sunset District"): 16,
    ("Alamo Square", "Presidio"): 18,
    ("Pacific Heights", "Chinatown"): 11,
    ("Pacific Heights", "Mission District"): 15,
    ("Pacific Heights", "Alamo Square"): 10,
    ("Pacific Heights", "Union Square"): 12,
    ("Pacific Heights", "Golden Gate Park"): 15,
    ("Pacific Heights", "Sunset District"): 21,
    ("Pacific Heights", "Presidio"): 11,
    ("Union Square", "Chinatown"): 7,
    ("Union Square", "Mission District"): 14,
    ("Union Square", "Alamo Square"): 15,
    ("Union Square", "Pacific Heights"): 15,
    ("Union Square", "Golden Gate Park"): 22,
    ("Union Square", "Sunset District"): 26,
    ("Union Square", "Presidio"): 24,
    ("Golden Gate Park", "Chinatown"): 23,
    ("Golden Gate Park", "Mission District"): 17,
    ("Golden Gate Park", "Alamo Square"): 10,
    ("Golden Gate Park", "Pacific Heights"): 16,
    ("Golden Gate Park", "Union Square"): 22,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "Presidio"): 11,
    ("Sunset District", "Chinatown"): 30,
    ("Sunset District", "Mission District"): 24,
    ("Sunset District", "Alamo Square"): 17,
    ("Sunset District", "Pacific Heights"): 21,
    ("Sunset District", "Union Square"): 30,
    ("Sunset District", "Golden Gate Park"): 11,
    ("Sunset District", "Presidio"): 16,
    ("Presidio", "Chinatown"): 21,
    ("Presidio", "Mission District"): 26,
    ("Presidio", "Alamo Square"): 18,
    ("Presidio", "Pacific Heights"): 11,
    ("Presidio", "Union Square"): 22,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Sunset District"): 15,
}

# Define the friends and their availability
friends = [
    {
        "name": "David",
        "location": "Mission District",
        "available_start": 8 * 60,  # 8:00 AM in minutes
        "available_end": 19 * 60 + 45,  # 7:45 PM in minutes
        "duration": 45,
    },
    {
        "name": "Kenneth",
        "location": "Alamo Square",
        "available_start": 14 * 60,  # 2:00 PM in minutes
        "available_end": 19 * 60 + 45,  # 7:45 PM in minutes
        "duration": 120,
    },
    {
        "name": "John",
        "location": "Pacific Heights",
        "available_start": 17 * 60,  # 5:00 PM in minutes
        "available_end": 20 * 60,  # 8:00 PM in minutes
        "duration": 15,
    },
    {
        "name": "Charles",
        "location": "Union Square",
        "available_start": 21 * 60 + 45,  # 9:45 PM in minutes
        "available_end": 22 * 60 + 45,  # 10:45 PM in minutes
        "duration": 60,
    },
    {
        "name": "Deborah",
        "location": "Golden Gate Park",
        "available_start": 7 * 60,  # 7:00 AM in minutes
        "available_end": 18 * 60 + 15,  # 6:15 PM in minutes
        "duration": 90,
    },
    {
        "name": "Karen",
        "location": "Sunset District",
        "available_start": 17 * 60 + 45,  # 5:45 PM in minutes
        "available_end": 21 * 60 + 15,  # 9:15 PM in minutes
        "duration": 15,
    },
    {
        "name": "Carol",
        "location": "Presidio",
        "available_start": 8 * 60 + 15,  # 8:15 AM in minutes
        "available_end": 9 * 60 + 15,  # 9:15 AM in minutes
        "duration": 30,
    },
]

# Initialize Z3 solver
s = Solver()

# Create variables for each meeting's start and end times
meetings = []
for friend in friends:
    start = Int(f"start_{friend['name']}")
    end = Int(f"end_{friend['name']}")
    meetings.append({
        "name": friend["name"],
        "location": friend["location"],
        "start": start,
        "end": end,
        "duration": friend["duration"],
        "available_start": friend["available_start"],
        "available_end": friend["available_end"],
    })

# Add constraints for each meeting
for meeting in meetings:
    s.add(meeting["start"] >= meeting["available_start"])
    s.add(meeting["end"] <= meeting["available_end"])
    s.add(meeting["end"] == meeting["start"] + meeting["duration"])

# Define the initial location and time
current_location = "Chinatown"
current_time = 9 * 60  # 9:00 AM in minutes

# Add constraints for travel times between meetings
# We'll try to meet Carol first, then David, then Deborah, then Kenneth, then John, then Karen, then Charles
order = ["Carol", "David", "Deborah", "Kenneth", "John", "Karen", "Charles"]

for i in range(len(order)):
    meeting = next(m for m in meetings if m["name"] == order[i])
    if i == 0:
        # First meeting: Carol at Presidio
        travel_time = travel_times[(current_location, meeting["location"])]
        s.add(meeting["start"] >= current_time + travel_time)
    else:
        # Subsequent meetings: travel from previous location
        prev_meeting = next(m for m in meetings if m["name"] == order[i-1])
        travel_time = travel_times[(prev_meeting["location"], meeting["location"])]
        s.add(meeting["start"] >= prev_meeting["end"] + travel_time)

# Check if the problem is satisfiable
if s.check() == sat:
    model = s.model()
    itinerary = []
    for meeting in meetings:
        start_time = model.eval(meeting["start"]).as_long()
        end_time = model.eval(meeting["end"]).as_long()
        # Convert minutes to HH:MM format
        start_hh = start_time // 60
        start_mm = start_time % 60
        end_hh = end_time // 60
        end_mm = end_time % 60
        itinerary.append({
            "action": "meet",
            "person": meeting["name"],
            "start_time": f"{start_hh:02d}:{start_mm:02d}",
            "end_time": f"{end_hh:02d}:{end_mm:02d}",
        })
    # Sort itinerary by start time
    itinerary.sort(key=lambda x: x["start_time"])
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No valid schedule found.")