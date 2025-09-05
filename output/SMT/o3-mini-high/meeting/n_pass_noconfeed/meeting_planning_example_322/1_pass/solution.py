from z3 import *
import json

def minutes_to_time(m):
    # Convert integer minute-of-day to "H:MM" 24-hour format (no leading zero for hour)
    h = m // 60
    mi = m % 60
    return f"{h}:{mi:02d}"

def main():
    opt = Optimize()

    # Travel times in minutes between locations
    travel_times = {
        ("Sunset District", "Russian Hill"): 24,
        ("Sunset District", "Chinatown"): 30,
        ("Sunset District", "Presidio"): 16,
        ("Sunset District", "Fisherman's Wharf"): 29,
        ("Russian Hill", "Sunset District"): 23,
        ("Russian Hill", "Chinatown"): 9,
        ("Russian Hill", "Presidio"): 14,
        ("Russian Hill", "Fisherman's Wharf"): 7,
        ("Chinatown", "Sunset District"): 29,
        ("Chinatown", "Russian Hill"): 7,
        ("Chinatown", "Presidio"): 19,
        ("Chinatown", "Fisherman's Wharf"): 8,
        ("Presidio", "Sunset District"): 15,
        ("Presidio", "Russian Hill"): 14,
        ("Presidio", "Chinatown"): 21,
        ("Presidio", "Fisherman's Wharf"): 19,
        ("Fisherman's Wharf", "Sunset District"): 27,
        ("Fisherman's Wharf", "Russian Hill"): 7,
        ("Fisherman's Wharf", "Chinatown"): 12,
        ("Fisherman's Wharf", "Presidio"): 17,
    }

    # Friend meeting data: availability window (in minutes after midnight), minimum meeting duration, and meeting location
    friends = {
        "William": {
            "location": "Russian Hill",
            "avail_start": 18 * 60 + 30,  # 18:30 -> 1110 minutes
            "avail_end": 20 * 60 + 45,    # 20:45 -> 1245 minutes
            "min_duration": 105
        },
        "Michelle": {
            "location": "Chinatown",
            "avail_start": 8 * 60 + 15,   # 8:15 -> 495 minutes
            "avail_end": 14 * 60,         # 14:00 -> 840 minutes
            "min_duration": 15
        },
        "George": {
            "location": "Presidio",
            "avail_start": 10 * 60 + 30,  # 10:30 -> 630 minutes
            "avail_end": 18 * 60 + 45,    # 18:45 -> 1125 minutes
            "min_duration": 30
        },
        "Robert": {
            "location": "Fisherman's Wharf",
            "avail_start": 9 * 60,        # 9:00 -> 540 minutes
            "avail_end": 13 * 60 + 45,      # 13:45 -> 825 minutes
            "min_duration": 30
        }
    }

    # Starting point details
    START_LOCATION = "Sunset District"
    START_TIME = 9 * 60  # 9:00 AM -> 540 minutes

    # Create Z3 variables for each friend:
    # meet[friend] is a Boolean indicating whether the meeting is scheduled.
    # s[friend] and e[friend] are the start and end times of the meeting (in minutes).
    meet_vars = {}
    s_vars = {}
    e_vars = {}

    for friend, info in friends.items():
        meet_var = Bool(f"meet_{friend}")
        s_var = Int(f"s_{friend}")
        e_var = Int(f"e_{friend}")
        meet_vars[friend] = meet_var
        s_vars[friend] = s_var
        e_vars[friend] = e_var

        avail_start = info["avail_start"]
        avail_end = info["avail_end"]
        min_dur = info["min_duration"]
        location = info["location"]

        # Calculate lower bound for arrival if coming directly from the starting location.
        travel_from_start = travel_times[(START_LOCATION, location)]
        lower_bound = max(avail_start, START_TIME + travel_from_start)
        # If meeting is scheduled, enforce availability and duration constraints.
        opt.add(Implies(meet_var, s_var >= lower_bound))
        opt.add(Implies(meet_var, e_var <= avail_end))
        opt.add(Implies(meet_var, e_var - s_var >= min_dur))
        # If not scheduled, fix start and end times to 0.
        opt.add(Implies(Not(meet_var), s_var == 0))
        opt.add(Implies(Not(meet_var), e_var == 0))

    # Add travel and ordering constraints between every pair of meetings.
    # For any two scheduled meetings, one must occur before the other with travel time accounted for.
    friend_list = list(friends.keys())
    for i in range(len(friend_list)):
        for j in range(i + 1, len(friend_list)):
            f_i = friend_list[i]
            f_j = friend_list[j]
            loc_i = friends[f_i]["location"]
            loc_j = friends[f_j]["location"]
            travel_ij = travel_times[(loc_i, loc_j)]
            travel_ji = travel_times[(loc_j, loc_i)]
            # Either meeting f_i is before f_j OR meeting f_j is before f_i.
            opt.add(Implies(And(meet_vars[f_i], meet_vars[f_j]),
                            Or(e_vars[f_i] + travel_ij <= s_vars[f_j],
                               e_vars[f_j] + travel_ji <= s_vars[f_i])))

    # Objective: maximize the number of meetings scheduled
    total_meetings = Sum([If(meet_vars[f], 1, 0) for f in friend_list])
    opt.maximize(total_meetings)

    # Solve and extract the optimal schedule.
    if opt.check() == sat:
        model = opt.model()
        itinerary = []
        for friend in friend_list:
            if model.evaluate(meet_vars[friend]):
                s_time = model.evaluate(s_vars[friend]).as_long()
                e_time = model.evaluate(e_vars[friend]).as_long()
                itinerary.append({
                    "person": friend,
                    "location": friends[friend]["location"],
                    "start_time": minutes_to_time(s_time),
                    "end_time": minutes_to_time(e_time)
                })
        # Sort the itinerary by start time (in minutes)
        def sort_key(item):
            h, m = item["start_time"].split(":")
            return int(h) * 60 + int(m)
        itinerary.sort(key=sort_key)
        # Format the output itinerary with the "action" field added.
        output = {"itinerary": [{"action": "meet", **item} for item in itinerary]}
        print(json.dumps(output, indent=2))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()