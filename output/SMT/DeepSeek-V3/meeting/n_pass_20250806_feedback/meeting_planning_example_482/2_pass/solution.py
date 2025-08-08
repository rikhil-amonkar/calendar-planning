from z3 import *
import json

# Define the locations and travel times
locations = ["Haight-Ashbury", "Mission District", "Bayview", "Pacific Heights", "Russian Hill", "Fisherman's Wharf"]
travel_times = {
    ("Haight-Ashbury", "Mission District"): 11,
    ("Haight-Ashbury", "Bayview"): 18,
    ("Haight-Ashbury", "Pacific Heights"): 12,
    ("Haight-Ashbury", "Russian Hill"): 17,
    ("Haight-Ashbury", "Fisherman's Wharf"): 23,
    ("Mission District", "Haight-Ashbury"): 12,
    ("Mission District", "Bayview"): 15,
    ("Mission District", "Pacific Heights"): 16,
    ("Mission District", "Russian Hill"): 15,
    ("Mission District", "Fisherman's Wharf"): 22,
    ("Bayview", "Haight-Ashbury"): 19,
    ("Bayview", "Mission District"): 13,
    ("Bayview", "Pacific Heights"): 23,
    ("Bayview", "Russian Hill"): 23,
    ("Bayview", "Fisherman's Wharf"): 25,
    ("Pacific Heights", "Haight-Ashbury"): 11,
    ("Pacific Heights", "Mission District"): 15,
    ("Pacific Heights", "Bayview"): 22,
    ("Pacific Heights", "Russian Hill"): 7,
    ("Pacific Heights", "Fisherman's Wharf"): 13,
    ("Russian Hill", "Haight-Ashbury"): 17,
    ("Russian Hill", "Mission District"): 16,
    ("Russian Hill", "Bayview"): 23,
    ("Russian Hill", "Pacific Heights"): 7,
    ("Russian Hill", "Fisherman's Wharf"): 7,
    ("Fisherman's Wharf", "Haight-Ashbury"): 22,
    ("Fisherman's Wharf", "Mission District"): 22,
    ("Fisherman's Wharf", "Bayview"): 26,
    ("Fisherman's Wharf", "Pacific Heights"): 12,
    ("Fisherman's Wharf", "Russian Hill"): 7,
}

# Define friends and their constraints
friends = [
    {
        "name": "Stephanie",
        "location": "Mission District",
        "available_start": "08:15",
        "available_end": "13:45",
        "min_duration": 90,
    },
    {
        "name": "Sandra",
        "location": "Bayview",
        "available_start": "13:00",
        "available_end": "19:30",
        "min_duration": 15,
    },
    {
        "name": "Richard",
        "location": "Pacific Heights",
        "available_start": "07:15",
        "available_end": "10:15",
        "min_duration": 75,
    },
    {
        "name": "Brian",
        "location": "Russian Hill",
        "available_start": "12:15",
        "available_end": "16:00",
        "min_duration": 120,
    },
    {
        "name": "Jason",
        "location": "Fisherman's Wharf",
        "available_start": "08:30",
        "available_end": "17:45",
        "min_duration": 60,
    },
]

# Convert time strings to minutes since 9:00 AM (540 minutes)
def time_to_minutes(time_str):
    hh, mm = map(int, time_str.split(":"))
    return hh * 60 + mm

start_time = time_to_minutes("09:00")  # 540 minutes (9:00 AM)

# Initialize Z3 solver
s = Solver()

# Create variables for each meeting: start and end times
meetings = []
for friend in friends:
    start = Int(f"start_{friend['name']}")
    end = Int(f"end_{friend['name']}")
    duration = friend["min_duration"]
    available_start = time_to_minutes(friend["available_start"])
    available_end = time_to_minutes(friend["available_end"])
    
    # Constraints: meeting must be within friend's availability
    s.add(start >= available_start)
    s.add(end <= available_end)
    s.add(end == start + duration)
    
    meetings.append({
        "name": friend["name"],
        "location": friend["location"],
        "start": start,
        "end": end,
    })

# Add constraints for travel times between meetings
for i in range(len(meetings)):
    for j in range(len(meetings)):
        if i != j:
            # Travel from meeting i to meeting j
            loc_i = meetings[i]["location"]
            loc_j = meetings[j]["location"]
            travel_time = travel_times.get((loc_i, loc_j), 0)
            
            # Ensure meeting j starts after meeting i ends + travel time
            s.add(Or(
                meetings[j]["start"] >= meetings[i]["end"] + travel_time,
                meetings[i]["start"] >= meetings[j]["end"] + travel_times.get((loc_j, loc_i), 0)
            ))

# Ensure all meetings start after 9:00 AM
for meeting in meetings:
    s.add(meeting["start"] >= start_time)

# Try to meet all friends (maximize the number of meetings)
# We'll prioritize meeting all friends if possible
# If not, we'll try subsets (but here we assume it's possible to meet all)

# Solve the model
if s.check() == sat:
    m = s.model()
    itinerary = []
    for meeting in meetings:
        start_val = m.evaluate(meeting["start"]).as_long()
        end_val = m.evaluate(meeting["end"]).as_long()
        
        # Convert minutes back to HH:MM format
        def minutes_to_time(minutes):
            hh = minutes // 60
            mm = minutes % 60
            return f"{hh:02d}:{mm:02d}"
        
        start_time_str = minutes_to_time(start_val)
        end_time_str = minutes_to_time(end_val)
        
        itinerary.append({
            "action": "meet",
            "person": meeting["name"],
            "start_time": start_time_str,
            "end_time": end_time_str,
        })
    
    # Sort itinerary by start time
    itinerary.sort(key=lambda x: x["start_time"])
    
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print('{"itinerary": []}')