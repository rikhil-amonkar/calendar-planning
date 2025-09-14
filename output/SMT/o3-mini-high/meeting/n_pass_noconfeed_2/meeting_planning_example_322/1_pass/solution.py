from z3 import *
import json

def minutes_to_time(mins):
    hours = mins // 60
    minutes = mins % 60
    return f"{hours}:{minutes:02d}"

def main():
    # Define travel times (in minutes) for each pair (origin, destination)
    travel = {
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
    
    # Define friends with meeting location, availability window (in minutes after midnight),
    # and the minimum meeting duration (in minutes)
    friends = {
        "William": {
            "location": "Russian Hill",
            "avail_start": 18 * 60 + 30,  # 18:30 -> 1110
            "avail_end": 20 * 60 + 45,    # 20:45 -> 1245
            "duration": 105
        },
        "Michelle": {
            "location": "Chinatown",
            "avail_start": 8 * 60 + 15,   # 08:15 -> 495
            "avail_end": 14 * 60,         # 14:00 -> 840
            "duration": 15
        },
        "George": {
            "location": "Presidio",
            "avail_start": 10 * 60 + 30,  # 10:30 -> 630
            "avail_end": 18 * 60 + 45,    # 18:45 -> 1125
            "duration": 30
        },
        "Robert": {
            "location": "Fisherman's Wharf",
            "avail_start": 9 * 60,        # 09:00 -> 540
            "avail_end": 13 * 60 + 45,      # 13:45 -> 825
            "duration": 30
        }
    }
    
    # Starting point and time: You arrive at Sunset District at 9:00 (540 minutes)
    start_location = "Sunset District"
    start_time_location = 9 * 60  # 540
    
    opt = Optimize()

    # Create Z3 variables for each friend: meeting start time and order number.
    # The order variable represents the sequence in which meetings are scheduled (1...4).
    S = {}      # Start times
    order = {}  # Order in the schedule
    for f in friends:
        S[f] = Int(f"start_{f}")
        order[f] = Int(f"order_{f}")
        # Each meeting must be scheduled within its availability window.
        opt.add(S[f] >= friends[f]["avail_start"])
        opt.add(S[f] + friends[f]["duration"] <= friends[f]["avail_end"])
        # Order numbers: from 1 to number of friends.
        opt.add(order[f] >= 1, order[f] <= len(friends))
    
    # Ensure that all order variables are distinct (i.e. form a permutation).
    opt.add(Distinct([order[f] for f in friends]))
    
    # For any two friends, enforce that if one is scheduled before the other then their meeting start times are ordered.
    friend_list = list(friends.keys())
    for i in range(len(friend_list)):
        for j in range(len(friend_list)):
            if i != j:
                f_i = friend_list[i]
                f_j = friend_list[j]
                opt.add(Implies(order[f_i] < order[f_j], S[f_i] < S[f_j]))
    
    # For the first meeting in the itinerary, ensure you account for travel time from the Sunset District.
    for f, props in friends.items():
        loc = props["location"]
        travel_time_from_start = travel.get((start_location, loc), 999)
        opt.add(Implies(order[f] == 1, S[f] >= start_time_location + travel_time_from_start))
    
    # Add travel constraints between consecutive meetings.
    # If friend f_i and friend f_j are scheduled consecutively (i.e. order difference is 1),
    # then the start time of f_j must be at least the end time of f_i plus travel time.
    for i in range(len(friend_list)):
        for j in range(len(friend_list)):
            if i != j:
                f_i = friend_list[i]
                f_j = friend_list[j]
                loc_i = friends[f_i]["location"]
                loc_j = friends[f_j]["location"]
                travel_time_between = travel.get((loc_i, loc_j), 999)
                opt.add(Implies(order[f_i] + 1 == order[f_j],
                                S[f_i] + friends[f_i]["duration"] + travel_time_between <= S[f_j]))
    
    # Define a variable representing the overall finish time (end of the last meeting)
    finish = Int("finish")
    for f in friends:
        opt.add(finish >= S[f] + friends[f]["duration"])
    
    # Optimize the schedule by minimizing the finish time.
    opt.minimize(finish)
    
    # Check and extract the model.
    if opt.check() == sat:
        m = opt.model()
        # Build the schedule as a list of tuples: (order, start_time, end_time, location, friend)
        schedule = []
        for f in friends:
            s_time = m[S[f]].as_long()
            e_time = s_time + friends[f]["duration"]
            schedule.append((m[order[f]].as_long(), s_time, e_time, friends[f]["location"], f))
        # Sort the schedule based on the order number.
        schedule.sort(key=lambda x: x[0])
        
        itinerary = []
        for (_, s_time, e_time, loc, friend_name) in schedule:
            itinerary.append({
                "action": "meet",
                "location": loc,
                "person": friend_name,
                "start_time": minutes_to_time(s_time),
                "end_time": minutes_to_time(e_time)
            })
        
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        # If no feasible schedule is found, output an empty itinerary.
        print(json.dumps({"itinerary": []}, indent=2))

if __name__ == "__main__":
    main()