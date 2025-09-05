from z3 import *
import json

# Define travel times between locations (in minutes)
travel_times = {
    ("Russian Hill", "Presidio"): 14,
    ("Russian Hill", "Chinatown"): 9,
    ("Russian Hill", "Pacific Heights"): 7,
    ("Russian Hill", "Richmond District"): 14,
    ("Russian Hill", "Fisherman's Wharf"): 7,
    ("Russian Hill", "Golden Gate Park"): 21,
    ("Russian Hill", "Bayview"): 23,
    
    ("Presidio", "Russian Hill"): 14,
    ("Presidio", "Chinatown"): 21,
    ("Presidio", "Pacific Heights"): 11,
    ("Presidio", "Richmond District"): 7,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Bayview"): 31,
    
    ("Chinatown", "Russian Hill"): 7,
    ("Chinatown", "Presidio"): 19,
    ("Chinatown", "Pacific Heights"): 10,
    ("Chinatown", "Richmond District"): 20,
    ("Chinatown", "Fisherman's Wharf"): 8,
    ("Chinatown", "Golden Gate Park"): 23,
    ("Chinatown", "Bayview"): 22,
    
    ("Pacific Heights", "Russian Hill"): 7,
    ("Pacific Heights", "Presidio"): 11,
    ("Pacific Heights", "Chinatown"): 11,
    ("Pacific Heights", "Richmond District"): 12,
    ("Pacific Heights", "Fisherman's Wharf"): 13,
    ("Pacific Heights", "Golden Gate Park"): 15,
    ("Pacific Heights", "Bayview"): 22,
    
    ("Richmond District", "Russian Hill"): 13,
    ("Richmond District", "Presidio"): 7,
    ("Richmond District", "Chinatown"): 20,
    ("Richmond District", "Pacific Heights"): 10,
    ("Richmond District", "Fisherman's Wharf"): 18,
    ("Richmond District", "Golden Gate Park"): 9,
    ("Richmond District", "Bayview"): 26,
    
    ("Fisherman's Wharf", "Russian Hill"): 7,
    ("Fisherman's Wharf", "Presidio"): 17,
    ("Fisherman's Wharf", "Chinatown"): 12,
    ("Fisherman's Wharf", "Pacific Heights"): 12,
    ("Fisherman's Wharf", "Richmond District"): 18,
    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    ("Fisherman's Wharf", "Bayview"): 26,
    
    ("Golden Gate Park", "Russian Hill"): 19,
    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "Chinatown"): 23,
    ("Golden Gate Park", "Pacific Heights"): 16,
    ("Golden Gate Park", "Richmond District"): 7,
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "Bayview"): 23,
    
    ("Bayview", "Russian Hill"): 23,
    ("Bayview", "Presidio"): 31,
    ("Bayview", "Chinatown"): 18,
    ("Bayview", "Pacific Heights"): 23,
    ("Bayview", "Richmond District"): 25,
    ("Bayview", "Fisherman's Wharf"): 25,
    ("Bayview", "Golden Gate Park"): 22,
}

# Friends' meeting constraints.
# Times are in minutes from midnight.
# Russian Hill arrival is 9:00 = 540.
friends = [
    { "name": "Matthew", "location": "Presidio", 
      "avail_start": 660, "avail_end": 1260, "min_meeting": 90 },  # 11:00 to 21:00
    { "name": "Margaret", "location": "Chinatown", 
      "avail_start": 555, "avail_end": 1125, "min_meeting": 90 },  # 9:15 to 18:45
    { "name": "Nancy", "location": "Pacific Heights", 
      "avail_start": 855, "avail_end": 1020, "min_meeting": 15 },  # 14:15 to 17:00
    { "name": "Helen", "location": "Richmond District", 
      "avail_start": 1185, "avail_end": 1320, "min_meeting": 60 },  # 19:45 to 22:00
    { "name": "Rebecca", "location": "Fisherman's Wharf", 
      "avail_start": 1275, "avail_end": 1335, "min_meeting": 60 },  # 21:15 to 22:15
    { "name": "Kimberly", "location": "Golden Gate Park", 
      "avail_start": 780, "avail_end": 990, "min_meeting": 120 },   # 13:00 to 16:30
    { "name": "Kenneth", "location": "Bayview", 
      "avail_start": 870, "avail_end": 1080, "min_meeting": 60 }      # 14:30 to 18:00
]

# Create an optimizer instance
solver = Optimize()

# For each friend, create decision variables:
# x: Boolean indicating whether to meet that friend.
# start and end: meeting start and end times in minutes after midnight.
meeting_vars = []
for f in friends:
    x = Bool("x_" + f["name"])
    start = Int("start_" + f["name"])
    end = Int("end_" + f["name"])
    meeting_vars.append({
        "name": f["name"],
        "location": f["location"],
        "avail_start": f["avail_start"],
        "avail_end": f["avail_end"],
        "min_meeting": f["min_meeting"],
        "x": x,
        "start": start,
        "end": end
    })
    
# Add constraints for each meeting
for m in meeting_vars:
    # If meeting is selected, it must be within the friend's available window.
    solver.add(Implies(m["x"], m["start"] >= m["avail_start"]))
    solver.add(Implies(m["x"], m["end"] <= m["avail_end"]))
    solver.add(Implies(m["x"], m["end"] - m["start"] >= m["min_meeting"]))
    # Also, if meeting is selected, you must be able to reach the location from Russian Hill by start time.
    travel_from_start = travel_times[("Russian Hill", m["location"])]
    solver.add(Implies(m["x"], m["start"] >= 540 + travel_from_start))

# Add disjunctive constraints for each pair of meetings if both are met.
n = len(meeting_vars)
for i in range(n):
    for j in range(i + 1, n):
        m1 = meeting_vars[i]
        m2 = meeting_vars[j]
        travel_m1_to_m2 = travel_times[(m1["location"], m2["location"])]
        travel_m2_to_m1 = travel_times[(m2["location"], m1["location"])]
        # If both meetings are selected, then either m1 happens before m2 (with travel) or vice versa.
        solver.add(Implies(And(m1["x"], m2["x"]),
                           Or(m1["end"] + travel_m1_to_m2 <= m2["start"],
                              m2["end"] + travel_m2_to_m1 <= m1["start"])))

# Objective: maximize the number of meetings scheduled.
obj = Sum([If(m["x"], 1, 0) for m in meeting_vars])
solver.maximize(obj)

# Check for a solution and retrieve the model.
if solver.check() == sat:
    model = solver.model()
    
    # Extract selected meetings and their scheduled times.
    selected_meetings = []
    for m in meeting_vars:
        if is_true(model.eval(m["x"])):
            start_val = model.eval(m["start"]).as_long()
            end_val = model.eval(m["end"]).as_long()
            selected_meetings.append({
                "person": m["name"],
                "location": m["location"],
                "start": start_val,
                "end": end_val
            })
    
    # Sort the meetings by their start time.
    selected_meetings.sort(key=lambda x: x["start"])
    
    # Helper function to format time in H:MM (24-hour) format.
    def format_time(minutes):
        hr = minutes // 60
        mn = minutes % 60
        return f"{hr}:{mn:02d}"
    
    # Build itinerary list with formatted times.
    itinerary = []
    for meeting in selected_meetings:
        itinerary.append({
            "action": "meet",
            "location": meeting["location"],
            "person": meeting["person"],
            "start_time": format_time(meeting["start"]),
            "end_time": format_time(meeting["end"])
        })
    
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))
else:
    print(json.dumps({"itinerary": []}))