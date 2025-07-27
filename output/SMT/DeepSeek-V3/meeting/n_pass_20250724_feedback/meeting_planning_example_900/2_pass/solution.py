from z3 import *
import json

# Define the travel times between districts
travel_times = {
    ("Richmond District", "The Castro"): 16,
    ("Richmond District", "Nob Hill"): 17,
    ("Richmond District", "Marina District"): 9,
    ("Richmond District", "Pacific Heights"): 10,
    ("Richmond District", "Haight-Ashbury"): 10,
    ("Richmond District", "Mission District"): 20,
    ("Richmond District", "Chinatown"): 20,
    ("Richmond District", "Russian Hill"): 13,
    ("Richmond District", "Alamo Square"): 13,
    ("Richmond District", "Bayview"): 27,
    ("The Castro", "Richmond District"): 16,
    ("The Castro", "Nob Hill"): 16,
    ("The Castro", "Marina District"): 21,
    ("The Castro", "Pacific Heights"): 16,
    ("The Castro", "Haight-Ashbury"): 6,
    ("The Castro", "Mission District"): 7,
    ("The Castro", "Chinatown"): 22,
    ("The Castro", "Russian Hill"): 18,
    ("The Castro", "Alamo Square"): 8,
    ("The Castro", "Bayview"): 19,
    ("Nob Hill", "Richmond District"): 14,
    ("Nob Hill", "The Castro"): 17,
    ("Nob Hill", "Marina District"): 11,
    ("Nob Hill", "Pacific Heights"): 8,
    ("Nob Hill", "Haight-Ashbury"): 13,
    ("Nob Hill", "Mission District"): 13,
    ("Nob Hill", "Chinatown"): 6,
    ("Nob Hill", "Russian Hill"): 5,
    ("Nob Hill", "Alamo Square"): 11,
    ("Nob Hill", "Bayview"): 19,
    ("Marina District", "Richmond District"): 11,
    ("Marina District", "The Castro"): 22,
    ("Marina District", "Nob Hill"): 12,
    ("Marina District", "Pacific Heights"): 7,
    ("Marina District", "Haight-Ashbury"): 16,
    ("Marina District", "Mission District"): 20,
    ("Marina District", "Chinatown"): 15,
    ("Marina District", "Russian Hill"): 8,
    ("Marina District", "Alamo Square"): 15,
    ("Marina District", "Bayview"): 27,
    ("Pacific Heights", "Richmond District"): 12,
    ("Pacific Heights", "The Castro"): 16,
    ("Pacific Heights", "Nob Hill"): 8,
    ("Pacific Heights", "Marina District"): 6,
    ("Pacific Heights", "Haight-Ashbury"): 11,
    ("Pacific Heights", "Mission District"): 15,
    ("Pacific Heights", "Chinatown"): 11,
    ("Pacific Heights", "Russian Hill"): 7,
    ("Pacific Heights", "Alamo Square"): 10,
    ("Pacific Heights", "Bayview"): 22,
    ("Haight-Ashbury", "Richmond District"): 10,
    ("Haight-Ashbury", "The Castro"): 6,
    ("Haight-Ashbury", "Nob Hill"): 15,
    ("Haight-Ashbury", "Marina District"): 17,
    ("Haight-Ashbury", "Pacific Heights"): 12,
    ("Haight-Ashbury", "Mission District"): 11,
    ("Haight-Ashbury", "Chinatown"): 19,
    ("Haight-Ashbury", "Russian Hill"): 17,
    ("Haight-Ashbury", "Alamo Square"): 5,
    ("Haight-Ashbury", "Bayview"): 18,
    ("Mission District", "Richmond District"): 20,
    ("Mission District", "The Castro"): 7,
    ("Mission District", "Nob Hill"): 12,
    ("Mission District", "Marina District"): 19,
    ("Mission District", "Pacific Heights"): 16,
    ("Mission District", "Haight-Ashbury"): 12,
    ("Mission District", "Chinatown"): 16,
    ("Mission District", "Russian Hill"): 15,
    ("Mission District", "Alamo Square"): 11,
    ("Mission District", "Bayview"): 14,
    ("Chinatown", "Richmond District"): 20,
    ("Chinatown", "The Castro"): 22,
    ("Chinatown", "Nob Hill"): 9,
    ("Chinatown", "Marina District"): 12,
    ("Chinatown", "Pacific Heights"): 10,
    ("Chinatown", "Haight-Ashbury"): 19,
    ("Chinatown", "Mission District"): 17,
    ("Chinatown", "Russian Hill"): 7,
    ("Chinatown", "Alamo Square"): 17,
    ("Chinatown", "Bayview"): 20,
    ("Russian Hill", "Richmond District"): 14,
    ("Russian Hill", "The Castro"): 21,
    ("Russian Hill", "Nob Hill"): 5,
    ("Russian Hill", "Marina District"): 7,
    ("Russian Hill", "Pacific Heights"): 7,
    ("Russian Hill", "Haight-Ashbury"): 17,
    ("Russian Hill", "Mission District"): 16,
    ("Russian Hill", "Chinatown"): 9,
    ("Russian Hill", "Alamo Square"): 15,
    ("Russian Hill", "Bayview"): 23,
    ("Alamo Square", "Richmond District"): 11,
    ("Alamo Square", "The Castro"): 8,
    ("Alamo Square", "Nob Hill"): 11,
    ("Alamo Square", "Marina District"): 15,
    ("Alamo Square", "Pacific Heights"): 10,
    ("Alamo Square", "Haight-Ashbury"): 5,
    ("Alamo Square", "Mission District"): 10,
    ("Alamo Square", "Chinatown"): 15,
    ("Alamo Square", "Russian Hill"): 13,
    ("Alamo Square", "Bayview"): 16,
    ("Bayview", "Richmond District"): 25,
    ("Bayview", "The Castro"): 19,
    ("Bayview", "Nob Hill"): 20,
    ("Bayview", "Marina District"): 27,
    ("Bayview", "Pacific Heights"): 23,
    ("Bayview", "Haight-Ashbury"): 19,
    ("Bayview", "Mission District"): 13,
    ("Bayview", "Chinatown"): 19,
    ("Bayview", "Russian Hill"): 23,
    ("Bayview", "Alamo Square"): 16,
}

# Define friends and their availability
friends = [
    {"name": "Matthew", "location": "The Castro", "start": 16.5, "end": 20.0, "duration": 0.75},
    {"name": "Rebecca", "location": "Nob Hill", "start": 15.25, "end": 19.25, "duration": 1.75},
    {"name": "Brian", "location": "Marina District", "start": 14.25, "end": 22.0, "duration": 0.5},
    {"name": "Emily", "location": "Pacific Heights", "start": 11.25, "end": 19.75, "duration": 0.25},
    {"name": "Karen", "location": "Haight-Ashbury", "start": 11.75, "end": 17.5, "duration": 0.5},
    {"name": "Stephanie", "location": "Mission District", "start": 13.0, "end": 15.75, "duration": 1.25},
    {"name": "James", "location": "Chinatown", "start": 14.5, "end": 19.0, "duration": 2.0},
    {"name": "Steven", "location": "Russian Hill", "start": 14.0, "end": 20.0, "duration": 0.5},
    {"name": "Elizabeth", "location": "Alamo Square", "start": 13.0, "end": 17.25, "duration": 2.0},
    {"name": "William", "location": "Bayview", "start": 18.25, "end": 20.25, "duration": 1.5},
]

# Initialize Z3 solver
s = Optimize()

# Create variables for each meeting's start and end times
meetings = []
for friend in friends:
    start = Real(f"start_{friend['name']}")
    end = Real(f"end_{friend['name']}")
    s.add(start >= friend["start"])
    s.add(end <= friend["end"])
    s.add(end == start + friend["duration"])
    meetings.append({"name": friend["name"], "location": friend["location"], "start": start, "end": end})

# Add constraints for travel times between consecutive meetings
# We'll model the order of meetings as a permutation
order = IntVector("order", len(meetings))
s.add(Distinct(order))
for i in range(len(meetings)):
    s.add(order[i] >= 0)
    s.add(order[i] < len(meetings))

# Add travel time constraints based on the order
for i in range(len(meetings) - 1):
    current = order[i]
    next_ = order[i + 1]
    s.add(meetings[next_]["start"] >= meetings[current]["end"] + 
          travel_times[(meetings[current]["location"], meetings[next_]["location"])] / 60)

# Start at Richmond District at 9:00 AM
current_location = "Richmond District"
current_time = 9.0
first_meeting = order[0]
s.add(meetings[first_meeting]["start"] >= current_time + 
      travel_times[(current_location, meetings[first_meeting]["location"])] / 60)

# Maximize the number of meetings met (by minimizing the number of skipped meetings)
# Since we want to meet all friends if possible, we don't need to skip any
# So we'll just check satisfiability

if s.check() == sat:
    model = s.model()
    itinerary = []
    # Get the order of meetings from the model
    meeting_order = sorted([(model.evaluate(order[i]).as_long(), i) for i in range(len(meetings))])
    meeting_order = [x[1] for x in sorted(meeting_order)]
    for idx in meeting_order:
        meeting = meetings[idx]
        start_val = model[meeting["start"]].as_fraction()
        end_val = model[meeting["end"]].as_fraction()
        start_time = float(start_val.numerator) / float(start_val.denominator)
        end_time = float(end_val.numerator) / float(end_val.denominator)
        # Convert to HH:MM format
        start_hour = int(start_time)
        start_minute = int((start_time - start_hour) * 60)
        end_hour = int(end_time)
        end_minute = int((end_time - end_hour) * 60)
        itinerary.append({
            "action": "meet",
            "person": meeting["name"],
            "start_time": f"{start_hour:02d}:{start_minute:02d}",
            "end_time": f"{end_hour:02d}:{end_minute:02d}"
        })
    # Sort itinerary by start time
    itinerary.sort(key=lambda x: x["start_time"])
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print('{"itinerary": []}')