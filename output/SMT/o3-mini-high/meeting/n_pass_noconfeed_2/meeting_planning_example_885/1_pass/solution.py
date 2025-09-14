from z3 import *
import json

# Travel times (in minutes) between locations
travel_times = {
    ("Russian Hill", "Marina District"): 7,
    ("Russian Hill", "Financial District"): 11,
    ("Russian Hill", "Alamo Square"): 15,
    ("Russian Hill", "Golden Gate Park"): 21,
    ("Russian Hill", "The Castro"): 21,
    ("Russian Hill", "Bayview"): 23,
    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "Haight-Ashbury"): 17,
    ("Russian Hill", "Nob Hill"): 5,
    
    ("Marina District", "Russian Hill"): 8,
    ("Marina District", "Financial District"): 17,
    ("Marina District", "Alamo Square"): 15,
    ("Marina District", "Golden Gate Park"): 18,
    ("Marina District", "The Castro"): 22,
    ("Marina District", "Bayview"): 27,
    ("Marina District", "Sunset District"): 19,
    ("Marina District", "Haight-Ashbury"): 16,
    ("Marina District", "Nob Hill"): 12,
    
    ("Financial District", "Russian Hill"): 11,
    ("Financial District", "Marina District"): 15,
    ("Financial District", "Alamo Square"): 17,
    ("Financial District", "Golden Gate Park"): 23,
    ("Financial District", "The Castro"): 20,
    ("Financial District", "Bayview"): 19,
    ("Financial District", "Sunset District"): 30,
    ("Financial District", "Haight-Ashbury"): 19,
    ("Financial District", "Nob Hill"): 8,
    
    ("Alamo Square", "Russian Hill"): 13,
    ("Alamo Square", "Marina District"): 15,
    ("Alamo Square", "Financial District"): 17,
    ("Alamo Square", "Golden Gate Park"): 9,
    ("Alamo Square", "The Castro"): 8,
    ("Alamo Square", "Bayview"): 16,
    ("Alamo Square", "Sunset District"): 16,
    ("Alamo Square", "Haight-Ashbury"): 5,
    ("Alamo Square", "Nob Hill"): 11,
    
    ("Golden Gate Park", "Russian Hill"): 19,
    ("Golden Gate Park", "Marina District"): 16,
    ("Golden Gate Park", "Financial District"): 26,
    ("Golden Gate Park", "Alamo Square"): 9,
    ("Golden Gate Park", "The Castro"): 13,
    ("Golden Gate Park", "Bayview"): 23,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "Haight-Ashbury"): 7,
    ("Golden Gate Park", "Nob Hill"): 20,
    
    ("The Castro", "Russian Hill"): 18,
    ("The Castro", "Marina District"): 21,
    ("The Castro", "Financial District"): 21,
    ("The Castro", "Alamo Square"): 8,
    ("The Castro", "Golden Gate Park"): 11,
    ("The Castro", "Bayview"): 19,
    ("The Castro", "Sunset District"): 17,
    ("The Castro", "Haight-Ashbury"): 6,
    ("The Castro", "Nob Hill"): 16,
    
    ("Bayview", "Russian Hill"): 23,
    ("Bayview", "Marina District"): 27,
    ("Bayview", "Financial District"): 19,
    ("Bayview", "Alamo Square"): 16,
    ("Bayview", "Golden Gate Park"): 22,
    ("Bayview", "The Castro"): 19,
    ("Bayview", "Sunset District"): 23,
    ("Bayview", "Haight-Ashbury"): 19,
    ("Bayview", "Nob Hill"): 20,
    
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "Marina District"): 21,
    ("Sunset District", "Financial District"): 30,
    ("Sunset District", "Alamo Square"): 17,
    ("Sunset District", "Golden Gate Park"): 11,
    ("Sunset District", "The Castro"): 17,
    ("Sunset District", "Bayview"): 22,
    ("Sunset District", "Haight-Ashbury"): 15,
    ("Sunset District", "Nob Hill"): 27,
    
    ("Haight-Ashbury", "Russian Hill"): 17,
    ("Haight-Ashbury", "Marina District"): 17,
    ("Haight-Ashbury", "Financial District"): 21,
    ("Haight-Ashbury", "Alamo Square"): 5,
    ("Haight-Ashbury", "Golden Gate Park"): 7,
    ("Haight-Ashbury", "The Castro"): 6,
    ("Haight-Ashbury", "Bayview"): 18,
    ("Haight-Ashbury", "Sunset District"): 15,
    ("Haight-Ashbury", "Nob Hill"): 15,
    
    ("Nob Hill", "Russian Hill"): 5,
    ("Nob Hill", "Marina District"): 11,
    ("Nob Hill", "Financial District"): 9,
    ("Nob Hill", "Alamo Square"): 11,
    ("Nob Hill", "Golden Gate Park"): 17,
    ("Nob Hill", "The Castro"): 17,
    ("Nob Hill", "Bayview"): 19,
    ("Nob Hill", "Sunset District"): 24,
    ("Nob Hill", "Haight-Ashbury"): 13
}

# Friend meeting details.
# Times are represented in minutes from midnight.
# 9:00 AM is 540.
friends = [
    {"name": "Mark", "location": "Marina District", "avail_start": 1125, "avail_end": 1260, "min_dur": 90},
    {"name": "Karen", "location": "Financial District", "avail_start": 570, "avail_end": 765, "min_dur": 90},
    {"name": "Barbara", "location": "Alamo Square", "avail_start": 600, "avail_end": 1170, "min_dur": 90},
    {"name": "Nancy", "location": "Golden Gate Park", "avail_start": 1005, "avail_end": 1200, "min_dur": 105},
    {"name": "David", "location": "The Castro", "avail_start": 540, "avail_end": 1080, "min_dur": 120},
    {"name": "Linda", "location": "Bayview", "avail_start": 1095, "avail_end": 1185, "min_dur": 45},
    {"name": "Kevin", "location": "Sunset District", "avail_start": 600, "avail_end": 1065, "min_dur": 120},
    {"name": "Matthew", "location": "Haight-Ashbury", "avail_start": 615, "avail_end": 930, "min_dur": 45},
    {"name": "Andrew", "location": "Nob Hill", "avail_start": 705, "avail_end": 1005, "min_dur": 105}
]

# Create an Optimize solver
opt = Optimize()

# For each friend, create variables:
# att (Bool): whether to meet this person,
# start (Int): meeting start time in minutes since midnight,
# end (Int): meeting end time in minutes since midnight.
att_vars = {}
start_vars = {}
end_vars = {}

# Our arrival at Russian Hill is fixed at 9:00 (540).
arrival_time = 540

for friend in friends:
    name = friend["name"]
    att_vars[name] = Bool(f"att_{name}")
    start_vars[name] = Int(f"start_{name}")
    end_vars[name] = Int(f"end_{name}")
    # Compute the lower bound if we were to go straight from Russian Hill.
    # This lower bound is the maximum of the available start and (arrival_time + travel time from Russian Hill).
    travel_from_rh = travel_times[("Russian Hill", friend["location"])]
    lower_bound = max(friend["avail_start"], arrival_time + travel_from_rh)
    # If meeting occurs, enforce that the meeting time window fits within the friend's available window
    # and meets the required minimum duration.
    opt.add(Implies(att_vars[name],
                    And(
                        start_vars[name] >= lower_bound,
                        end_vars[name] <= friend["avail_end"],
                        end_vars[name] - start_vars[name] >= friend["min_dur"]
                    )))

# Add disjunctive scheduling constraints for every pair of meetings.
# For any two scheduled meetings, either one must come before the other (including travel time).
friend_names = [friend["name"] for friend in friends]
for i in range(len(friend_names)):
    for j in range(i + 1, len(friend_names)):
        name_i = friend_names[i]
        name_j = friend_names[j]
        # Get locations for friend i and friend j.
        loc_i = next(friend["location"] for friend in friends if friend["name"] == name_i)
        loc_j = next(friend["location"] for friend in friends if friend["name"] == name_j)
        # Get travel times between these locations.
        travel_ij = travel_times[(loc_i, loc_j)]
        travel_ji = travel_times[(loc_j, loc_i)]
        # If both meetings are scheduled, enforce that the meetings do not overlap,
        # leaving enough time for the required travel between locations.
        opt.add(Implies(And(att_vars[name_i], att_vars[name_j]),
                        Or(
                            end_vars[name_i] + travel_ij <= start_vars[name_j],
                            end_vars[name_j] + travel_ji <= start_vars[name_i]
                        )))

# Objective: maximize the number of meetings scheduled.
objective = Sum([If(att_vars[friend["name"]], 1, 0) for friend in friends])
opt.maximize(objective)

# Check for a solution and extract the model.
if opt.check() == sat:
    m = opt.model()
    scheduled = []
    for friend in friends:
        name = friend["name"]
        if is_true(m.evaluate(att_vars[name])):
            st = m.evaluate(start_vars[name]).as_long()
            en = m.evaluate(end_vars[name]).as_long()
            scheduled.append({
                "person": name,
                "location": friend["location"],
                "start": st,
                "end": en
            })
    # Sort scheduled meetings by their start time.
    scheduled.sort(key=lambda x: x["start"])

    # Helper function to format minutes since midnight to "H:MM" 24-hour format.
    def format_time(t):
        hour = t // 60
        minute = t % 60
        return f"{hour}:{minute:02d}"

    itinerary = []
    for item in scheduled:
        itinerary.append({
            "action": "meet",
            "location": item["location"],
            "person": item["person"],
            "start_time": format_time(item["start"]),
            "end_time": format_time(item["end"])
        })

    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))
else:
    print(json.dumps({"itinerary": []}))
    
if __name__ == '__main__':
    pass