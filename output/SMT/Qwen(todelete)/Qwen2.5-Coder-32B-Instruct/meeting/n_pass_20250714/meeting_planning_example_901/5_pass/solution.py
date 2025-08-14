from z3 import *

# Define the time points in minutes from 9:00 AM
time_points = {
    "9:00AM": 0,
    "9:15AM": 15,
    "10:30AM": 90,
    "11:30AM": 120,
    "1:45PM": 225,
    "2:45PM": 345,
    "3:15PM": 375,
    "5:30PM": 630,
    "6:15PM": 675,
    "6:45PM": 765,
    "7:15PM": 795,
    "7:30AM": 60,
    "8:00AM": 60,
    "8:30AM": 90,
    "9:15PM": 915,
    "8:30PM": 870
}

# Define the friends and their availability
friends = {
    "Emily": (time_points["9:15AM"], time_points["1:45PM"], 120),
    "Helen": (time_points["1:45PM"], time_points["6:45PM"], 30),
    "Kimberly": (time_points["6:45PM"], time_points["9:15PM"], 75),
    "James": (time_points["10:30AM"], time_points["11:30AM"], 30),
    "Linda": (time_points["7:30AM"], time_points["7:15PM"], 15),
    "Paul": (time_points["2:45PM"], time_points["6:45PM"], 90),
    "Anthony": (time_points["8:00AM"], time_points["2:45PM"], 105),
    "Nancy": (time_points["8:30AM"], time_points["1:45PM"], 120),
    "William": (time_points["5:30PM"], time_points["8:30PM"], 120),
    "Margaret": (time_points["3:15PM"], time_points["6:15PM"], 45)
}

# Define the travel times
travel_times = {
    ("Russian Hill", "Pacific Heights"): 7,
    ("Russian Hill", "North Beach"): 5,
    ("Russian Hill", "Golden Gate Park"): 21,
    ("Russian Hill", "Embarcadero"): 8,
    ("Russian Hill", "Haight-Ashbury"): 17,
    ("Russian Hill", "Fisherman's Wharf"): 7,
    ("Russian Hill", "Mission District"): 16,
    ("Russian Hill", "Alamo Square"): 15,
    ("Russian Hill", "Bayview"): 23,
    ("Russian Hill", "Richmond District"): 14,
    ("Pacific Heights", "Russian Hill"): 7,
    ("Pacific Heights", "North Beach"): 9,
    ("Pacific Heights", "Golden Gate Park"): 15,
    ("Pacific Heights", "Embarcadero"): 10,
    ("Pacific Heights", "Haight-Ashbury"): 11,
    ("Pacific Heights", "Fisherman's Wharf"): 13,
    ("Pacific Heights", "Mission District"): 15,
    ("Pacific Heights", "Alamo Square"): 10,
    ("Pacific Heights", "Bayview"): 22,
    ("Pacific Heights", "Richmond District"): 12,
    ("North Beach", "Russian Hill"): 4,
    ("North Beach", "Pacific Heights"): 8,
    ("North Beach", "Golden Gate Park"): 22,
    ("North Beach", "Embarcadero"): 6,
    ("North Beach", "Haight-Ashbury"): 18,
    ("North Beach", "Fisherman's Wharf"): 5,
    ("North Beach", "Mission District"): 18,
    ("North Beach", "Alamo Square"): 16,
    ("North Beach", "Bayview"): 25,
    ("North Beach", "Richmond District"): 18,
    ("Golden Gate Park", "Russian Hill"): 19,
    ("Golden Gate Park", "Pacific Heights"): 16,
    ("Golden Gate Park", "North Beach"): 23,
    ("Golden Gate Park", "Embarcadero"): 25,
    ("Golden Gate Park", "Haight-Ashbury"): 7,
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "Mission District"): 17,
    ("Golden Gate Park", "Alamo Square"): 9,
    ("Golden Gate Park", "Bayview"): 23,
    ("Golden Gate Park", "Richmond District"): 7,
    ("Embarcadero", "Russian Hill"): 8,
    ("Embarcadero", "Pacific Heights"): 11,
    ("Embarcadero", "North Beach"): 5,
    ("Embarcadero", "Golden Gate Park"): 25,
    ("Embarcadero", "Haight-Ashbury"): 21,
    ("Embarcadero", "Fisherman's Wharf"): 6,
    ("Embarcadero", "Mission District"): 20,
    ("Embarcadero", "Alamo Square"): 19,
    ("Embarcadero", "Bayview"): 21,
    ("Embarcadero", "Richmond District"): 21,
    ("Haight-Ashbury", "Russian Hill"): 17,
    ("Haight-Ashbury", "Pacific Heights"): 12,
    ("Haight-Ashbury", "North Beach"): 19,
    ("Haight-Ashbury", "Golden Gate Park"): 7,
    ("Haight-Ashbury", "Embarcadero"): 20,
    ("Haight-Ashbury", "Fisherman's Wharf"): 23,
    ("Haight-Ashbury", "Mission District"): 11,
    ("Haight-Ashbury", "Alamo Square"): 5,
    ("Haight-Ashbury", "Bayview"): 18,
    ("Haight-Ashbury", "Richmond District"): 10,
    ("Fisherman's Wharf", "Russian Hill"): 7,
    ("Fisherman's Wharf", "Pacific Heights"): 12,
    ("Fisherman's Wharf", "North Beach"): 6,
    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    ("Fisherman's Wharf", "Embarcadero"): 8,
    ("Fisherman's Wharf", "Haight-Ashbury"): 22,
    ("Fisherman's Wharf", "Mission District"): 22,
    ("Fisherman's Wharf", "Alamo Square"): 21,
    ("Fisherman's Wharf", "Bayview"): 26,
    ("Fisherman's Wharf", "Richmond District"): 18,
    ("Mission District", "Russian Hill"): 15,
    ("Mission District", "Pacific Heights"): 16,
    ("Mission District", "North Beach"): 17,
    ("Mission District", "Golden Gate Park"): 17,
    ("Mission District", "Embarcadero"): 19,
    ("Mission District", "Haight-Ashbury"): 12,
    ("Mission District", "Fisherman's Wharf"): 22,
    ("Mission District", "Alamo Square"): 11,
    ("Mission District", "Bayview"): 14,
    ("Mission District", "Richmond District"): 20,
    ("Alamo Square", "Russian Hill"): 13,
    ("Alamo Square", "Pacific Heights"): 10,
    ("Alamo Square", "North Beach"): 15,
    ("Alamo Square", "Golden Gate Park"): 9,
    ("Alamo Square", "Embarcadero"): 16,
    ("Alamo Square", "Haight-Ashbury"): 5,
    ("Alamo Square", "Fisherman's Wharf"): 19,
    ("Alamo Square", "Mission District"): 10,
    ("Alamo Square", "Bayview"): 16,
    ("Alamo Square", "Richmond District"): 11,
    ("Bayview", "Russian Hill"): 23,
    ("Bayview", "Pacific Heights"): 23,
    ("Bayview", "North Beach"): 22,
    ("Bayview", "Golden Gate Park"): 22,
    ("Bayview", "Embarcadero"): 19,
    ("Bayview", "Haight-Ashbury"): 19,
    ("Bayview", "Fisherman's Wharf"): 25,
    ("Bayview", "Mission District"): 13,
    ("Bayview", "Alamo Square"): 16,
    ("Bayview", "Richmond District"): 25,
    ("Richmond District", "Russian Hill"): 13,
    ("Richmond District", "Pacific Heights"): 10,
    ("Richmond District", "North Beach"): 17,
    ("Richmond District", "Golden Gate Park"): 9,
    ("Richmond District", "Embarcadero"): 19,
    ("Richmond District", "Haight-Ashbury"): 10,
    ("Richmond District", "Fisherman's Wharf"): 18,
    ("Richmond District", "Mission District"): 20,
    ("Richmond District", "Alamo Square"): 13,
    ("Richmond District", "Bayview"): 27
}

# Create a solver instance
solver = Solver()

# Define variables for each friend
meetings = {friend: Int(f"meet_{friend}") for friend in friends}

# Define binary variables to indicate if a friend is met
met = {friend: Bool(f"met_{friend}") for friend in friends}

# Define the current location and start time
current_location = "Russian Hill"
current_time = time_points["9:00AM"]

# Define the possible locations
locations = ["Russian Hill", "Pacific Heights", "North Beach", "Golden Gate Park", 
             "Embarcadero", "Haight-Ashbury", "Fisherman's Wharf", "Mission District", 
             "Alamo Square", "Bayview", "Richmond District"]

# Define the next location variables
next_locations = [Int(f"next_location_{i}") for i in range(len(friends))]

# Add constraints for each friend
for i, (friend, (start, end, duration)) in enumerate(friends.items()):
    solver.add(meetings[friend] >= start)
    solver.add(meetings[friend] <= end - duration)
    solver.add(met[friend] == And(meetings[friend] >= start, meetings[friend] <= end - duration))
    
    if i == 0:
        # For the first friend, only consider travel from Russian Hill
        travel_time = Int(f"travel_time_{i}")
        solver.add(travel_time == If(next_locations[i] == locations.index("Pacific Heights"), travel_times[("Russian Hill", "Pacific Heights")],
                                    If(next_locations[i] == locations.index("North Beach"), travel_times[("Russian Hill", "North Beach")],
                                       If(next_locations[i] == locations.index("Golden Gate Park"), travel_times[("Russian Hill", "Golden Gate Park")],
                                          If(next_locations[i] == locations.index("Embarcadero"), travel_times[("Russian Hill", "Embarcadero")],
                                             If(next_locations[i] == locations.index("Haight-Ashbury"), travel_times[("Russian Hill", "Haight-Ashbury")],
                                                If(next_locations[i] == locations.index("Fisherman's Wharf"), travel_times[("Russian Hill", "Fisherman's Wharf")],
                                                   If(next_locations[i] == locations.index("Mission District"), travel_times[("Russian Hill", "Mission District")],
                                                      If(next_locations[i] == locations.index("Alamo Square"), travel_times[("Russian Hill", "Alamo Square")],
                                                         If(next_locations[i] == locations.index("Bayview"), travel_times[("Russian Hill", "Bayview")],
                                                            If(next_locations[i] == locations.index("Richmond District"), travel_times[("Russian Hill", "Richmond District")], 0)))))))))
        solver.add(meetings[friend] >= current_time + travel_time)
    else:
        # For subsequent friends, consider travel from the previous friend's location
        prev_friend = list(friends.keys())[i-1]
        travel_time = Int(f"travel_time_{i}")
        solver.add(travel_time == If(next_locations[i] == locations.index("Pacific Heights"), travel_times[(locations[next_locations[i-1]], "Pacific Heights")],
                                    If(next_locations[i] == locations.index("North Beach"), travel_times[(locations[next_locations[i-1]], "North Beach")],
                                       If(next_locations[i] == locations.index("Golden Gate Park"), travel_times[(locations[next_locations[i-1]], "Golden Gate Park")],
                                          If(next_locations[i] == locations.index("Embarcadero"), travel_times[(locations[next_locations[i-1]], "Embarcadero")],
                                             If(next_locations[i] == locations.index("Haight-Ashbury"), travel_times[(locations[next_locations[i-1]], "Haight-Ashbury")],
                                                If(next_locations[i] == locations.index("Fisherman's Wharf"), travel_times[(locations[next_locations[i-1]], "Fisherman's Wharf")],
                                                   If(next_locations[i] == locations.index("Mission District"), travel_times[(locations[next_locations[i-1]], "Mission District")],
                                                      If(next_locations[i] == locations.index("Alamo Square"), travel_times[(locations[next_locations[i-1]], "Alamo Square")],
                                                         If(next_locations[i] == locations.index("Bayview"), travel_times[(locations[next_locations[i-1]], "Bayview")],
                                                            If(next_locations[i] == locations.index("Richmond District"), travel_times[(locations[next_locations[i-1]], "Richmond District")], 0)))))))))
        solver.add(meetings[friend] >= meetings[prev_friend] + friends[prev_friend][2] + travel_time)

# Ensure exactly 7 friends are met
solver.add(Sum([If(met[friend], 1, 0) for friend in friends]) == 7)

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    print("SOLUTION:")
    met_friends = []
    for friend in friends:
        if model[met[friend]]:
            meeting_time = model[meetings[friend]].as_long()
            meeting_start = meeting_time
            meeting_end = meeting_start + friends[friend][2]
            meeting_start_str = f"{meeting_start // 60}:{meeting_start % 60:02d}AM" if meeting_start < 720 else f"{(meeting_start // 60) - 12}:{meeting_start % 60:02d}PM"
            meeting_end_str = f"{meeting_end // 60}:{meeting_end % 60:02d}AM" if meeting_end < 720 else f"{(meeting_end // 60) - 12}:{meeting_end % 60:02d}PM"
            print(f"Meet {friend} from {meeting_start_str} to {meeting_end_str}")
            met_friends.append(friend)
    print(f"Friends met: {met_friends}")
else:
    print("No solution found")