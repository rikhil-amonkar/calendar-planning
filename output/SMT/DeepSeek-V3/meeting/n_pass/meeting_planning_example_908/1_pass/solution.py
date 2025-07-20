import z3
from datetime import datetime, timedelta

# Define the friends and their availability
friends = {
    "Mark": {
        "location": "Fisherman's Wharf",
        "start": "08:15",
        "end": "10:00",
        "duration": 30,
    },
    "Stephanie": {
        "location": "Presidio",
        "start": "12:15",
        "end": "15:00",
        "duration": 75,
    },
    "Betty": {
        "location": "Bayview",
        "start": "07:15",
        "end": "20:30",
        "duration": 15,
    },
    "Lisa": {
        "location": "Haight-Ashbury",
        "start": "15:30",
        "end": "18:30",
        "duration": 45,
    },
    "William": {
        "location": "Russian Hill",
        "start": "18:45",
        "end": "20:00",
        "duration": 60,
    },
    "Brian": {
        "location": "The Castro",
        "start": "09:15",
        "end": "13:15",
        "duration": 30,
    },
    "Joseph": {
        "location": "Marina District",
        "start": "10:45",
        "end": "15:00",
        "duration": 90,
    },
    "Ashley": {
        "location": "Richmond District",
        "start": "09:45",
        "end": "11:15",
        "duration": 45,
    },
    "Patricia": {
        "location": "Union Square",
        "start": "16:30",
        "end": "20:00",
        "duration": 120,
    },
    "Karen": {
        "location": "Sunset District",
        "start": "16:30",
        "end": "22:00",
        "duration": 105,
    },
}

# Define travel times (in minutes) between locations
travel_times = {
    "Financial District": {
        "Fisherman's Wharf": 10,
        "Presidio": 22,
        "Bayview": 19,
        "Haight-Ashbury": 19,
        "Russian Hill": 11,
        "The Castro": 20,
        "Marina District": 15,
        "Richmond District": 21,
        "Union Square": 9,
        "Sunset District": 30,
    },
    "Fisherman's Wharf": {
        "Financial District": 11,
        "Presidio": 17,
        "Bayview": 26,
        "Haight-Ashbury": 22,
        "Russian Hill": 7,
        "The Castro": 27,
        "Marina District": 9,
        "Richmond District": 18,
        "Union Square": 13,
        "Sunset District": 27,
    },
    "Presidio": {
        "Financial District": 23,
        "Fisherman's Wharf": 19,
        "Bayview": 31,
        "Haight-Ashbury": 15,
        "Russian Hill": 14,
        "The Castro": 21,
        "Marina District": 11,
        "Richmond District": 7,
        "Union Square": 22,
        "Sunset District": 15,
    },
    "Bayview": {
        "Financial District": 19,
        "Fisherman's Wharf": 25,
        "Presidio": 32,
        "Haight-Ashbury": 19,
        "Russian Hill": 23,
        "The Castro": 19,
        "Marina District": 27,
        "Richmond District": 25,
        "Union Square": 18,
        "Sunset District": 23,
    },
    "Haight-Ashbury": {
        "Financial District": 21,
        "Fisherman's Wharf": 23,
        "Presidio": 15,
        "Bayview": 18,
        "Russian Hill": 17,
        "The Castro": 6,
        "Marina District": 17,
        "Richmond District": 10,
        "Union Square": 19,
        "Sunset District": 15,
    },
    "Russian Hill": {
        "Financial District": 11,
        "Fisherman's Wharf": 7,
        "Presidio": 14,
        "Bayview": 23,
        "Haight-Ashbury": 17,
        "The Castro": 21,
        "Marina District": 7,
        "Richmond District": 14,
        "Union Square": 10,
        "Sunset District": 23,
    },
    "The Castro": {
        "Financial District": 21,
        "Fisherman's Wharf": 24,
        "Presidio": 20,
        "Bayview": 19,
        "Haight-Ashbury": 6,
        "Russian Hill": 18,
        "Marina District": 21,
        "Richmond District": 16,
        "Union Square": 19,
        "Sunset District": 17,
    },
    "Marina District": {
        "Financial District": 17,
        "Fisherman's Wharf": 10,
        "Presidio": 10,
        "Bayview": 27,
        "Haight-Ashbury": 16,
        "Russian Hill": 8,
        "The Castro": 22,
        "Richmond District": 11,
        "Union Square": 16,
        "Sunset District": 19,
    },
    "Richmond District": {
        "Financial District": 22,
        "Fisherman's Wharf": 18,
        "Presidio": 7,
        "Bayview": 27,
        "Haight-Ashbury": 10,
        "Russian Hill": 13,
        "The Castro": 16,
        "Marina District": 9,
        "Union Square": 21,
        "Sunset District": 11,
    },
    "Union Square": {
        "Financial District": 9,
        "Fisherman's Wharf": 15,
        "Presidio": 24,
        "Bayview": 15,
        "Haight-Ashbury": 18,
        "Russian Hill": 13,
        "The Castro": 17,
        "Marina District": 18,
        "Richmond District": 20,
        "Sunset District": 27,
    },
    "Sunset District": {
        "Financial District": 30,
        "Fisherman's Wharf": 29,
        "Presidio": 16,
        "Bayview": 22,
        "Haight-Ashbury": 15,
        "Russian Hill": 24,
        "The Castro": 17,
        "Marina District": 21,
        "Richmond District": 12,
        "Union Square": 30,
    },
}

# Initialize Z3 solver
solver = z3.Optimize()

# Convert time strings to minutes since 9:00 AM (540 minutes)
def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

# Convert minutes back to time string
def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

# Define variables for each meeting
meetings = {}
for name in friends:
    start = z3.Int(f"start_{name}")
    end = z3.Int(f"end_{name}")
    meetings[name] = {
        "start": start,
        "end": end,
        "location": friends[name]["location"],
        "duration": friends[name]["duration"],
    }
    # Constraint: meeting duration
    solver.add(end == start + friends[name]["duration"])
    # Constraint: meeting within friend's availability
    solver.add(start >= time_to_minutes(friends[name]["start"]))
    solver.add(end <= time_to_minutes(friends[name]["end"]))

# Constraint: you start at Financial District at 9:00 AM (540 minutes)
current_location = "Financial District"
current_time = 540  # 9:00 AM in minutes

# Define the order of meetings
meeting_order = z3.Array("meeting_order", z3.IntSort(), z3.StringSort())
meeting_times = z3.Array("meeting_times", z3.IntSort(), z3.IntSort())

# Ensure no overlapping meetings and account for travel time
for i, name1 in enumerate(friends):
    for j, name2 in enumerate(friends):
        if i != j:
            # Either meeting1 is before meeting2 or vice versa
            before = z3.Or(
                meetings[name1]["end"] + travel_times[meetings[name1]["location"]][meetings[name2]["location"]] <= meetings[name2]["start"],
                meetings[name2]["end"] + travel_times[meetings[name2]["location"]][meetings[name1]["location"]] <= meetings[name1]["start"],
            )
            solver.add(before)

# Maximize the number of friends met
solver.maximize(z3.Sum([z3.If(meetings[name]["start"] >= 0, 1, 0) for name in friends]))

# Check if a solution exists
if solver.check() == z3.sat:
    model = solver.model()
    itinerary = []
    for name in friends:
        start_val = model[meetings[name]["start"]].as_long()
        if start_val >= 0:
            end_val = model[meetings[name]["end"]].as_long()
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": minutes_to_time(start_val),
                "end_time": minutes_to_time(end_val),
            })
    # Sort itinerary by start time
    itinerary.sort(key=lambda x: time_to_minutes(x["start_time"]))
    print('SOLUTION:')
    print({"itinerary": itinerary})
else:
    print("No solution found")