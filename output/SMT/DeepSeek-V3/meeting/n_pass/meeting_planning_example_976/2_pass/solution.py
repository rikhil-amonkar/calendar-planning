from z3 import *
import datetime

# Define the locations and friends
locations = [
    "Embarcadero", "Bayview", "Chinatown", "Alamo Square", "Nob Hill", "Presidio",
    "Union Square", "The Castro", "North Beach", "Fisherman's Wharf", "Marina District"
]
friends = {
    "Matthew": {"location": "Bayview", "start": "19:15", "end": "22:00", "duration": 120},
    "Karen": {"location": "Chinatown", "start": "19:15", "end": "21:15", "duration": 90},
    "Sarah": {"location": "Alamo Square", "start": "20:00", "end": "21:45", "duration": 105},
    "Jessica": {"location": "Nob Hill", "start": "16:30", "end": "18:45", "duration": 120},
    "Stephanie": {"location": "Presidio", "start": "07:30", "end": "10:15", "duration": 60},
    "Mary": {"location": "Union Square", "start": "16:45", "end": "21:30", "duration": 60},
    "Charles": {"location": "The Castro", "start": "16:30", "end": "22:00", "duration": 105},
    "Nancy": {"location": "North Beach", "start": "14:45", "end": "20:00", "duration": 15},
    "Thomas": {"location": "Fisherman's Wharf", "start": "13:30", "end": "19:00", "duration": 30},
    "Brian": {"location": "Marina District", "start": "12:15", "end": "18:00", "duration": 60}
}

# Travel times dictionary (simplified for brevity)
travel_times = {
    ("Embarcadero", "Bayview"): 21,
    ("Embarcadero", "Chinatown"): 7,
    ("Embarcadero", "Alamo Square"): 19,
    ("Embarcadero", "Nob Hill"): 10,
    ("Embarcadero", "Presidio"): 20,
    ("Embarcadero", "Union Square"): 10,
    ("Embarcadero", "The Castro"): 25,
    ("Embarcadero", "North Beach"): 5,
    ("Embarcadero", "Fisherman's Wharf"): 6,
    ("Embarcadero", "Marina District"): 12,
    # Include reverse directions and other connections as needed
    ("Bayview", "Embarcadero"): 19,
    ("Chinatown", "Embarcadero"): 5,
    # Add all other necessary travel times
}

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    total_minutes = 540 + minutes  # 9:00 AM is 540 minutes
    h = total_minutes // 60
    m = total_minutes % 60
    return f"{h:02d}:{m:02d}"

# Use Optimize instead of Solver for maximization
opt = Optimize()

# Variables: start and end times for each friend meeting
meetings = {}
for friend in friends:
    start = Int(f"start_{friend}")
    duration = friends[friend]["duration"]
    end = Int(f"end_{friend}")
    meetings[friend] = {"start": start, "end": end}
    # Constraint: end = start + duration
    opt.add(end == start + duration)
    # Constraint: meeting must be within friend's availability
    opt.add(start >= time_to_minutes(friends[friend]["start"]) - 540)
    opt.add(end <= time_to_minutes(friends[friend]["end"]) - 540)

# Constraint: no overlapping meetings and travel time between meetings
for friend1 in friends:
    for friend2 in friends:
        if friend1 != friend2:
            loc1 = friends[friend1]["location"]
            loc2 = friends[friend2]["location"]
            travel_time = travel_times.get((loc1, loc2), 0)
            opt.add(Or(
                meetings[friend1]["end"] + travel_time <= meetings[friend2]["start"],
                meetings[friend2]["end"] + travel_time <= meetings[friend1]["start"]
            ))

# Maximize the total meeting time
total_meeting_time = Int("total_meeting_time")
opt.add(total_meeting_time == sum([meetings[friend]["end"] - meetings[friend]["start"] for friend in friends]))
opt.maximize(total_meeting_time)

# Check if a solution exists
if opt.check() == sat:
    m = opt.model()
    itinerary = []
    for friend in friends:
        start_val = m[meetings[friend]["start"]]
        end_val = m[meetings[friend]["end"]]
        if start_val is not None and end_val is not None:
            start = start_val.as_long()
            end = end_val.as_long()
            itinerary.append({
                "action": "meet",
                "person": friend,
                "start_time": minutes_to_time(start),
                "end_time": minutes_to_time(end)
            })
    # Sort itinerary by start time
    itinerary.sort(key=lambda x: time_to_minutes(x["start_time"]))
    print({"itinerary": itinerary})
else:
    print("No solution found")