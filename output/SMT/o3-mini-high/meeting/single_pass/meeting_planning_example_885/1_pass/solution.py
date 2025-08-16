from z3 import Optimize, Int, Bool, If, And, Or, Implies, Distinct
import json

# Helper function: convert minutes-since-midnight to "HH:MM" string.
def minutes_to_time(m):
    hh = m // 60
    mm = m % 60
    return f"{hh:02d}:{mm:02d}"

def main():
    # Create an Optimize object
    opt = Optimize()

    # Define friend data.
    # All times are in minutes since midnight.
    # For example, 9:00AM is 9*60 = 540.
    friends = {
        "Mark": {
            "location": "Marina District",
            "avail_start": 18*60 + 45,  # 18:45
            "avail_end": 21*60,         # 21:00
            "duration": 90
        },
        "Karen": {
            "location": "Financial District",
            "avail_start": 9*60 + 30,   # 09:30
            "avail_end": 12*60 + 45,    # 12:45
            "duration": 90
        },
        "Barbara": {
            "location": "Alamo Square",
            "avail_start": 10*60,       # 10:00
            "avail_end": 19*60 + 30,    # 19:30
            "duration": 90
        },
        "Nancy": {
            "location": "Golden Gate Park",
            "avail_start": 16*60 + 45,  # 16:45
            "avail_end": 20*60,         # 20:00
            "duration": 105
        },
        "David": {
            "location": "The Castro",
            "avail_start": 9*60,        # 09:00
            "avail_end": 18*60,         # 18:00
            "duration": 120
        },
        "Linda": {
            "location": "Bayview",
            "avail_start": 18*60 + 15,  # 18:15
            "avail_end": 19*60 + 45,    # 19:45
            "duration": 45
        },
        "Kevin": {
            "location": "Sunset District",
            "avail_start": 10*60,       # 10:00
            "avail_end": 17*60 + 45,    # 17:45
            "duration": 120
        },
        "Matthew": {
            "location": "Haight-Ashbury",
            "avail_start": 10*60 + 15,   # 10:15
            "avail_end": 15*60 + 30,    # 15:30
            "duration": 45
        },
        "Andrew": {
            "location": "Nob Hill",
            "avail_start": 11*60 + 45,  # 11:45
            "avail_end": 16*60 + 45,    # 16:45
            "duration": 105
        }
    }

    # Define travel times (in minutes) between locations.
    # The keys are (from, to) tuples.
    travel = {
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
        ("Nob Hill", "Haight-Ashbury"): 13,
    }

    # We start the day at Russian Hill at 9:00 (540 minutes).
    base_location = "Russian Hill"
    base_time = 540

    # Create Z3 variables for each friend:
    #  - meet_f is a Bool (True if we decide to meet that friend),
    #  - start_f is an Int for the meeting start time (in minutes),
    #  - order_f is an Int (if meeting is scheduled then a positive integer indicating its order; 0 means not scheduled)
    vars_dict = {}
    for f in friends:
        vars_dict[f] = {
            "meet": Bool("meet_" + f),
            "start": Int("start_" + f),
            "order": Int("order_" + f)
        }

    n = len(friends)
    
    # For each friend, if we schedule the meeting then enforce the friend’s time window
    for f, data in friends.items():
        avail_start = data["avail_start"]
        avail_end = data["avail_end"]
        duration = data["duration"]
        opt.add(
            If(vars_dict[f]["meet"],
               And(
                   vars_dict[f]["start"] >= avail_start,
                   vars_dict[f]["start"] + duration <= avail_end,
                   vars_dict[f]["order"] >= 1,
                   vars_dict[f]["order"] <= n
               ),
               vars_dict[f]["order"] == 0
            )
        )
        # Also, ensure meeting start time is nonnegative.
        opt.add(vars_dict[f]["start"] >= 0)

    # For every pair of meetings (if both are scheduled), enforce that their orders are distinct
    # and that travel time is respected between their meeting intervals.
    friend_list = list(friends.keys())
    for i in range(len(friend_list)):
        f = friend_list[i]
        for j in range(i+1, len(friend_list)):
            g = friend_list[j]
            # Distinct order if both f and g are scheduled
            opt.add(Or( 
                Not(vars_dict[f]["meet"]), 
                Not(vars_dict[g]["meet"]), 
                vars_dict[f]["order"] != vars_dict[g]["order"]
            ))
            # If f is scheduled before g, then finish time of f plus travel from f->g must be <= start time of g.
            travel_fg = travel[(friends[f]["location"], friends[g]["location"])]
            opt.add(
                Implies(
                    And(vars_dict[f]["meet"], vars_dict[g]["meet"], vars_dict[f]["order"] < vars_dict[g]["order"]),
                    vars_dict[f]["start"] + friends[f]["duration"] + travel_fg <= vars_dict[g]["start"]
                )
            )
            # Similarly, if g is before f then travel from g->f applies.
            travel_gf = travel[(friends[g]["location"], friends[f]["location"])]
            opt.add(
                Implies(
                    And(vars_dict[f]["meet"], vars_dict[g]["meet"], vars_dict[g]["order"] < vars_dict[f]["order"]),
                    vars_dict[g]["start"] + friends[g]["duration"] + travel_gf <= vars_dict[f]["start"]
                )
            )

    # For each friend that is scheduled first (order==1), enforce that we have enough time to reach that friend's location from Russian Hill.
    for f, data in friends.items():
        travel_from_base = travel[(base_location, data["location"])]
        opt.add(
            Implies(
                And(vars_dict[f]["meet"], vars_dict[f]["order"] == 1),
                base_time + travel_from_base <= vars_dict[f]["start"]
            )
        )
    
    # Objective: maximize the total number of meetings.
    total_meetings = sum([If(vars_dict[f]["meet"], 1, 0) for f in friends])
    opt.maximize(total_meetings)

    # Check and extract a model.
    if opt.check() == "sat":
        model = opt.model()
        schedule = []
        # Collect scheduled meetings from the model.
        for f in friends:
            if model.evaluate(vars_dict[f]["meet"]):
                order_val = model.evaluate(vars_dict[f]["order"]).as_long()
                start_val = model.evaluate(vars_dict[f]["start"]).as_long()
                end_val = start_val + friends[f]["duration"]
                schedule.append((order_val, f, start_val, end_val))
        # Sort the scheduled meetings by their order number.
        schedule.sort(key=lambda x: x[0])
        itinerary = []
        for order_val, friend, start_val, end_val in schedule:
            itinerary.append({
                "action": "meet",
                "person": friend,
                "start_time": minutes_to_time(start_val),
                "end_time": minutes_to_time(end_val)
            })
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()