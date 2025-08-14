from z3 import *

# Define the locations and their indices
locations = [
    "Financial District", "Fisherman's Wharf", "Presidio", "Bayview",
    "Haight-Ashbury", "Russian Hill", "The Castro", "Marina District",
    "Richmond District", "Union Square", "Sunset District"
]

# Define the travel times matrix
travel_times = {
    ("Financial District", "Fisherman's Wharf"): 10,
    ("Financial District", "Presidio"): 22,
    ("Financial District", "Bayview"): 19,
    ("Financial District", "Haight-Ashbury"): 19,
    ("Financial District", "Russian Hill"): 11,
    ("Financial District", "The Castro"): 20,
    ("Financial District", "Marina District"): 15,
    ("Financial District", "Richmond District"): 21,
    ("Financial District", "Union Square"): 9,
    ("Financial District", "Sunset District"): 30,
    ("Fisherman's Wharf", "Financial District"): 11,
    ("Fisherman's Wharf", "Presidio"): 17,
    ("Fisherman's Wharf", "Bayview"): 26,
    ("Fisherman's Wharf", "Haight-Ashbury"): 22,
    ("Fisherman's Wharf", "Russian Hill"): 7,
    ("Fisherman's Wharf", "The Castro"): 27,
    ("Fisherman's Wharf", "Marina District"): 9,
    ("Fisherman's Wharf", "Richmond District"): 18,
    ("Fisherman's Wharf", "Union Square"): 13,
    ("Fisherman's Wharf", "Sunset District"): 27,
    ("Presidio", "Financial District"): 23,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Presidio", "Bayview"): 31,
    ("Presidio", "Haight-Ashbury"): 15,
    ("Presidio", "Russian Hill"): 14,
    ("Presidio", "The Castro"): 21,
    ("Presidio", "Marina District"): 11,
    ("Presidio", "Richmond District"): 7,
    ("Presidio", "Union Square"): 22,
    ("Presidio", "Sunset District"): 15,
    ("Bayview", "Financial District"): 19,
    ("Bayview", "Fisherman's Wharf"): 25,
    ("Bayview", "Presidio"): 32,
    ("Bayview", "Haight-Ashbury"): 19,
    ("Bayview", "Russian Hill"): 23,
    ("Bayview", "The Castro"): 19,
    ("Bayview", "Marina District"): 27,
    ("Bayview", "Richmond District"): 25,
    ("Bayview", "Union Square"): 18,
    ("Bayview", "Sunset District"): 23,
    ("Haight-Ashbury", "Financial District"): 21,
    ("Haight-Ashbury", "Fisherman's Wharf"): 23,
    ("Haight-Ashbury", "Presidio"): 15,
    ("Haight-Ashbury", "Bayview"): 18,
    ("Haight-Ashbury", "Russian Hill"): 17,
    ("Haight-Ashbury", "The Castro"): 6,
    ("Haight-Ashbury", "Marina District"): 17,
    ("Haight-Ashbury", "Richmond District"): 10,
    ("Haight-Ashbury", "Union Square"): 19,
    ("Haight-Ashbury", "Sunset District"): 15,
    ("Russian Hill", "Financial District"): 11,
    ("Russian Hill", "Fisherman's Wharf"): 7,
    ("Russian Hill", "Presidio"): 14,
    ("Russian Hill", "Bayview"): 23,
    ("Russian Hill", "Haight-Ashbury"): 17,
    ("Russian Hill", "The Castro"): 21,
    ("Russian Hill", "Marina District"): 7,
    ("Russian Hill", "Richmond District"): 14,
    ("Russian Hill", "Union Square"): 10,
    ("Russian Hill", "Sunset District"): 23,
    ("The Castro", "Financial District"): 21,
    ("The Castro", "Fisherman's Wharf"): 24,
    ("The Castro", "Presidio"): 20,
    ("The Castro", "Bayview"): 19,
    ("The Castro", "Haight-Ashbury"): 6,
    ("The Castro", "Russian Hill"): 18,
    ("The Castro", "Marina District"): 21,
    ("The Castro", "Richmond District"): 16,
    ("The Castro", "Union Square"): 19,
    ("The Castro", "Sunset District"): 17,
    ("Marina District", "Financial District"): 17,
    ("Marina District", "Fisherman's Wharf"): 10,
    ("Marina District", "Presidio"): 10,
    ("Marina District", "Bayview"): 27,
    ("Marina District", "Haight-Ashbury"): 16,
    ("Marina District", "Russian Hill"): 8,
    ("Marina District", "The Castro"): 22,
    ("Marina District", "Richmond District"): 11,
    ("Marina District", "Union Square"): 16,
    ("Marina District", "Sunset District"): 19,
    ("Richmond District", "Financial District"): 22,
    ("Richmond District", "Fisherman's Wharf"): 18,
    ("Richmond District", "Presidio"): 7,
    ("Richmond District", "Bayview"): 27,
    ("Richmond District", "Haight-Ashbury"): 10,
    ("Richmond District", "Russian Hill"): 13,
    ("Richmond District", "The Castro"): 16,
    ("Richmond District", "Marina District"): 9,
    ("Richmond District", "Union Square"): 21,
    ("Richmond District", "Sunset District"): 11,
    ("Union Square", "Financial District"): 9,
    ("Union Square", "Fisherman's Wharf"): 15,
    ("Union Square", "Presidio"): 24,
    ("Union Square", "Bayview"): 15,
    ("Union Square", "Haight-Ashbury"): 18,
    ("Union Square", "Russian Hill"): 13,
    ("Union Square", "The Castro"): 17,
    ("Union Square", "Marina District"): 18,
    ("Union Square", "Richmond District"): 20,
    ("Union Square", "Sunset District"): 27,
    ("Sunset District", "Financial District"): 30,
    ("Sunset District", "Fisherman's Wharf"): 29,
    ("Sunset District", "Presidio"): 16,
    ("Sunset District", "Bayview"): 22,
    ("Sunset District", "Haight-Ashbury"): 15,
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "The Castro"): 17,
    ("Sunset District", "Marina District"): 21,
    ("Sunset District", "Richmond District"): 12,
    ("Sunset District", "Union Square"): 30,
}

# Define the friends and their availability
friends = {
    "Mark": {"location": "Fisherman's Wharf", "start": 8 * 60 + 15, "end": 10 * 60, "duration": 30},
    "Stephanie": {"location": "Presidio", "start": 12 * 60 + 15, "end": 15 * 60, "duration": 75},
    "Betty": {"location": "Bayview", "start": 7 * 60 + 15, "end": 20 * 60 + 30, "duration": 15},
    "Lisa": {"location": "Haight-Ashbury", "start": 15 * 60 + 30, "end": 18 * 60 + 30, "duration": 45},
    "William": {"location": "Russian Hill", "start": 18 * 60 + 45, "end": 20 * 60, "duration": 60},
    "Brian": {"location": "The Castro", "start": 9 * 60 + 15, "end": 13 * 60 + 15, "duration": 30},
    "Joseph": {"location": "Marina District", "start": 10 * 60 + 45, "end": 15 * 60, "duration": 90},
    "Ashley": {"location": "Richmond District", "start": 9 * 60 + 45, "end": 11 * 60 + 15, "duration": 45},
    "Patricia": {"location": "Union Square", "start": 16 * 60 + 30, "end": 20 * 60, "duration": 120},
    "Karen": {"location": "Sunset District", "start": 16 * 60 + 30, "end": 22 * 60, "duration": 105},
}

# Create a solver instance
solver = Solver()

# Define binary variables for each friend and each minute of the day
minutes_in_day = 24 * 60
meetings = [[Bool(f"{friend}_{minute}") for minute in range(minutes_in_day)] for friend in friends]

# Define the current location and time
current_location = "Financial District"
current_time = 9 * 60

# Add constraints for each friend
for friend_idx, (friend, details) in enumerate(friends.items()):
    location = details["location"]
    start = details["start"]
    end = details["end"]
    duration = details["duration"]

    # Ensure the meeting starts within the friend's available time
    meeting_times = [And(meetings[friend_idx][t], *[meetings[friend_idx][t + i] for i in range(1, duration)]) for t in range(start, end - duration + 1)]
    solver.add(Or(meeting_times))

    # Ensure the meeting does not overlap with other meetings
    for other_friend_idx in range(len(friends)):
        if other_friend_idx != friend_idx:
            for t in range(minutes_in_day):
                solver.add(Implies(meetings[friend_idx][t], Not(meetings[other_friend_idx][t])))

# Ensure exactly 9 meetings are scheduled
num_meetings = Sum([If(Or(meeting_times), 1, 0) for meeting_times in [Or(meetings[friend_idx][t] for t in range(friends[friend]["start"], friends[friend]["end"] - friends[friend]["duration"] + 1)) for friend_idx, friend in enumerate(friends)]])
solver.add(num_meetings == 9)

# Ensure travel time constraints are respected
for friend_idx, (friend, details) in enumerate(friends.items()):
    location = details["location"]
    start = details["start"]
    end = details["end"]
    duration = details["duration"]

    for t in range(start, end - duration + 1):
        for t_prime in range(t + duration, minutes_in_day):
            solver.add(Implies(meetings[friend_idx][t], And(
                Or([meetings[other_friend_idx][t_prime - travel_times[(current_location, location)]] for other_friend_idx, other_friend in enumerate(friends) if other_friend != friend]),
                Or([meetings[other_friend_idx][t_prime - travel_times[(location, current_location)]] for other_friend_idx, other_friend in enumerate(friends) if other_friend != friend])
            )))

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    schedule = []
    for friend_idx, (friend, details) in enumerate(friends.items()):
        for t in range(details["start"], details["end"] - details["duration"] + 1):
            if any(model.evaluate(meetings[friend_idx][t + i]) for i in range(details["duration"])):
                schedule.append((friend, t, t + details["duration"]))
                break
    schedule.sort(key=lambda x: x[1])
    print("SOLUTION:")
    for friend, start, end in schedule:
        print(f"{friend}: {start // 60}:{start % 60:02d} - {end // 60}:{end % 60:02d}")
else:
    print("No solution found.")