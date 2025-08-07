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

# Define friends with priority order (higher priority first)
friends = [
    {
        "name": "Richard",
        "location": "Pacific Heights",
        "available_start": "07:15",
        "available_end": "10:15",
        "min_duration": 75,
        "priority": 1
    },
    {
        "name": "Brian",
        "location": "Russian Hill",
        "available_start": "12:15",
        "available_end": "16:00",
        "min_duration": 120,
        "priority": 2
    },
    {
        "name": "Stephanie",
        "location": "Mission District",
        "available_start": "08:15",
        "available_end": "13:45",
        "min_duration": 90,
        "priority": 3
    },
    {
        "name": "Jason",
        "location": "Fisherman's Wharf",
        "available_start": "08:30",
        "available_end": "17:45",
        "min_duration": 60,
        "priority": 4
    },
    {
        "name": "Sandra",
        "location": "Bayview",
        "available_start": "13:00",
        "available_end": "19:30",
        "min_duration": 15,
        "priority": 5
    }
]

# Convert time strings to minutes since midnight
def time_to_minutes(time_str):
    hh, mm = map(int, time_str.split(":"))
    return hh * 60 + mm

start_time = time_to_minutes("09:00")  # 540 minutes (9:00 AM)

# Initialize Z3 solver and optimizer
s = Solver()
opt = Optimize()

# Create variables for each meeting
meetings = []
for friend in friends:
    start = Int(f"start_{friend['name']}")
    end = Int(f"end_{friend['name']}")
    duration = friend["min_duration"]
    available_start = time_to_minutes(friend["available_start"])
    available_end = time_to_minutes(friend["available_end"])
    
    # Basic constraints
    s.add(start >= available_start)
    s.add(end <= available_end)
    s.add(end == start + duration)
    
    meetings.append({
        "name": friend["name"],
        "location": friend["location"],
        "start": start,
        "end": end,
        "priority": friend["priority"]
    })

# Special constraint for Richard - must account for travel time
richard_idx = next(i for i, m in enumerate(meetings) if m["name"] == "Richard")
s.add(meetings[richard_idx]["start"] >= start_time + travel_times[("Haight-Ashbury", "Pacific Heights")])

# Create meeting order variables
order = [Int(f"order_{m['name']}") for m in meetings]
s.add(Distinct(order))
for o in order:
    s.add(o >= 0, o < len(meetings))

# Add travel time constraints based on ordering
for i in range(len(meetings)):
    for j in range(len(meetings)):
        if i != j:
            loc_i = meetings[i]["location"]
            loc_j = meetings[j]["location"]
            travel_time = travel_times.get((loc_i, loc_j), 0)
            
            # If meeting i comes before meeting j in order
            s.add(Implies(
                order[i] < order[j],
                meetings[j]["start"] >= meetings[i]["end"] + travel_time
            ))

# Ensure all meetings start after 9:00 AM
for meeting in meetings:
    s.add(meeting["start"] >= start_time)

# Optimize to meet as many friends as possible
num_met = Int("num_met")
s.add(num_met == Sum([If(meetings[i]["start"] >= start_time, 1, 0) for i in range(len(meetings))]))

# Try to meet higher priority friends first
priority_score = Sum([If(meetings[i]["start"] >= start_time, meetings[i]["priority"], 0) for i in range(len(meetings))])

# Add all constraints to the optimizer
opt.add(s.assertions())

# Set optimization goals
opt.maximize(num_met)
opt.maximize(priority_score)

# Solve the model
if opt.check() == sat:
    m = opt.model()
    itinerary = []
    for meeting in meetings:
        start_val = m.evaluate(meeting["start"]).as_long()
        end_val = m.evaluate(meeting["end"]).as_long()
        
        def minutes_to_time(minutes):
            hh = minutes // 60
            mm = minutes % 60
            return f"{hh:02d}:{mm:02d}"
        
        if start_val >= start_time:  # Only include meetings that were scheduled
            itinerary.append({
                "action": "meet",
                "person": meeting["name"],
                "start_time": minutes_to_time(start_val),
                "end_time": minutes_to_time(end_val),
            })
    
    # Sort itinerary by start time
    itinerary.sort(key=lambda x: x["start_time"])
    
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print('{"itinerary": []}')