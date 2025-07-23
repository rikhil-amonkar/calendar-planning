from z3 import *

# Define the locations
locations = ["Fisherman's Wharf", "The Castro", "Golden Gate Park", "Embarcadero", "Russian Hill", "Nob Hill", "Alamo Square", "North Beach"]

# Define the travel times
travel_times = {
    ("Fisherman's Wharf", "The Castro"): 26,
    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    ("Fisherman's Wharf", "Embarcadero"): 8,
    ("Fisherman's Wharf", "Russian Hill"): 7,
    ("Fisherman's Wharf", "Nob Hill"): 11,
    ("Fisherman's Wharf", "Alamo Square"): 20,
    ("Fisherman's Wharf", "North Beach"): 6,
    ("The Castro", "Fisherman's Wharf"): 24,
    ("The Castro", "Golden Gate Park"): 11,
    ("The Castro", "Embarcadero"): 22,
    ("The Castro", "Russian Hill"): 18,
    ("The Castro", "Nob Hill"): 16,
    ("The Castro", "Alamo Square"): 8,
    ("The Castro", "North Beach"): 20,
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "The Castro"): 13,
    ("Golden Gate Park", "Embarcadero"): 25,
    ("Golden Gate Park", "Russian Hill"): 19,
    ("Golden Gate Park", "Nob Hill"): 20,
    ("Golden Gate Park", "Alamo Square"): 10,
    ("Golden Gate Park", "North Beach"): 24,
    ("Embarcadero", "Fisherman's Wharf"): 6,
    ("Embarcadero", "The Castro"): 25,
    ("Embarcadero", "Golden Gate Park"): 25,
    ("Embarcadero", "Russian Hill"): 8,
    ("Embarcadero", "Nob Hill"): 10,
    ("Embarcadero", "Alamo Square"): 19,
    ("Embarcadero", "North Beach"): 5,
    ("Russian Hill", "Fisherman's Wharf"): 7,
    ("Russian Hill", "The Castro"): 21,
    ("Russian Hill", "Golden Gate Park"): 21,
    ("Russian Hill", "Embarcadero"): 8,
    ("Russian Hill", "Nob Hill"): 5,
    ("Russian Hill", "Alamo Square"): 15,
    ("Russian Hill", "North Beach"): 5,
    ("Nob Hill", "Fisherman's Wharf"): 11,
    ("Nob Hill", "The Castro"): 17,
    ("Nob Hill", "Golden Gate Park"): 17,
    ("Nob Hill", "Embarcadero"): 9,
    ("Nob Hill", "Russian Hill"): 5,
    ("Nob Hill", "Alamo Square"): 11,
    ("Nob Hill", "North Beach"): 8,
    ("Alamo Square", "Fisherman's Wharf"): 19,
    ("Alamo Square", "The Castro"): 8,
    ("Alamo Square", "Golden Gate Park"): 9,
    ("Alamo Square", "Embarcadero"): 17,
    ("Alamo Square", "Russian Hill"): 13,
    ("Alamo Square", "Nob Hill"): 11,
    ("Alamo Square", "North Beach"): 15,
    ("North Beach", "Fisherman's Wharf"): 5,
    ("North Beach", "The Castro"): 22,
    ("North Beach", "Golden Gate Park"): 22,
    ("North Beach", "Embarcadero"): 6,
    ("North Beach", "Russian Hill"): 4,
    ("North Beach", "Nob Hill"): 7,
    ("North Beach", "Alamo Square"): 16,
}

# Define the friends and their availability
friends = {
    "Laura": {"location": "The Castro", "start": 1945, "end": 2130, "min_duration": 105},
    "Daniel": {"location": "Golden Gate Park", "start": 2115, "end": 2145, "min_duration": 15},
    "William": {"location": "Embarcadero", "start": 700, "end": 900, "min_duration": 90},
    "Karen": {"location": "Russian Hill", "start": 1430, "end": 1945, "min_duration": 30},
    "Stephanie": {"location": "Nob Hill", "start": 730, "end": 930, "min_duration": 45},
    "Joseph": {"location": "Alamo Square", "start": 1130, "end": 1245, "min_duration": 15},
    "Kimberly": {"location": "North Beach", "start": 1545, "end": 1915, "min_duration": 30},
}

# Convert times to minutes since start of the day
def time_to_minutes(time):
    hours, minutes = divmod(time, 100)
    return hours * 60 + minutes

# Create a solver instance
solver = Solver()

# Define variables for the start and end times of each meeting
meeting_times = {}
for friend in friends:
    start = Int(f"{friend}_start")
    end = Int(f"{friend}_end")
    meeting_times[friend] = (start, end)
    solver.add(start >= time_to_minutes(friends[friend]["start"]))
    solver.add(end <= time_to_minutes(friends[friend]["end"]))
    solver.add(end - start >= friends[friend]["min_duration"])

# Define the initial location and time
current_location = "Fisherman's Wharf"
current_time = time_to_minutes(900)

# Define constraints for traveling between locations
for i, friend in enumerate(friends):
    start, end = meeting_times[friend]
    if i == 0:
        solver.add(current_time + travel_times[(current_location, friends[friend]["location"])] <= start)
    else:
        prev_friend = list(friends.keys())[i-1]
        prev_end = meeting_times[prev_friend][1]
        solver.add(prev_end + travel_times[(friends[prev_friend]["location"], friends[friend]["location"])] <= start)

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for friend in friends:
        start = model[meeting_times[friend][0]].as_long()
        end = model[meeting_times[friend][1]].as_long()
        itinerary.append({
            "action": "meet",
            "person": friend,
            "start_time": f"{start // 60:02}:{start % 60:02}",
            "end_time": f"{end // 60:02}:{end % 60:02}"
        })
    print({"itinerary": itinerary})
else:
    print("No solution found")