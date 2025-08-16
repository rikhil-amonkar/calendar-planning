from z3 import *
import json

def minutes_to_hhmm(m):
    h = m // 60
    mm = m % 60
    return f"{h:02d}:{mm:02d}"

def main():
    # Define friends with their meeting parameters:
    # Times are in minutes after midnight.
    # For example, 9:00 AM = 540, 13:00 = 780, etc.
    friends = [
        {"name": "Kevin", "location": "Mission District", "avail_start": 1245, "avail_end": 1305, "duration": 60},
        {"name": "Mark", "location": "Fisherman's Wharf", "avail_start": 1035, "avail_end": 1200, "duration": 90},
        {"name": "Jessica", "location": "Russian Hill", "avail_start": 540, "avail_end": 900, "duration": 120},
        {"name": "Jason", "location": "Marina District", "avail_start": 915, "avail_end": 1305, "duration": 120},
        {"name": "John", "location": "North Beach", "avail_start": 585, "avail_end": 1080, "duration": 15},
        {"name": "Karen", "location": "Chinatown", "avail_start": 1005, "avail_end": 1140, "duration": 75},
        {"name": "Sarah", "location": "Pacific Heights", "avail_start": 1050, "avail_end": 1095, "duration": 45},
        {"name": "Amanda", "location": "The Castro", "avail_start": 1200, "avail_end": 1275, "duration": 60},
        {"name": "Nancy", "location": "Nob Hill", "avail_start": 585, "avail_end": 780, "duration": 45},
        {"name": "Rebecca", "location": "Sunset District", "avail_start": 525, "avail_end": 900, "duration": 75}
    ]
    
    # Travel times (in minutes) as provided.
    # Note: The travel time from location A to location B may differ from B to A.
    travel = {
        "Union Square": {
            "Mission District": 14,
            "Fisherman's Wharf": 15,
            "Russian Hill": 13,
            "Marina District": 18,
            "North Beach": 10,
            "Chinatown": 7,
            "Pacific Heights": 15,
            "The Castro": 17,
            "Nob Hill": 9,
            "Sunset District": 27
        },
        "Mission District": {
            "Union Square": 15,
            "Fisherman's Wharf": 22,
            "Russian Hill": 15,
            "Marina District": 19,
            "North Beach": 17,
            "Chinatown": 16,
            "Pacific Heights": 16,
            "The Castro": 7,
            "Nob Hill": 12,
            "Sunset District": 24
        },
        "Fisherman's Wharf": {
            "Union Square": 13,
            "Mission District": 22,  # assuming symmetry with the Mission District->Fisherman's Wharf value
            "Russian Hill": 7,
            "Marina District": 9,
            "North Beach": 6,
            "Chinatown": 12,
            "Pacific Heights": 12,
            "The Castro": 27,
            "Nob Hill": 11,
            "Sunset District": 27
        },
        "Russian Hill": {
            "Union Square": 10,
            "Mission District": 16,
            "Fisherman's Wharf": 7,
            "Marina District": 7,
            "North Beach": 5,
            "Chinatown": 9,
            "Pacific Heights": 7,
            "The Castro": 21,
            "Nob Hill": 5,
            "Sunset District": 23
        },
        "Marina District": {
            "Union Square": 16,
            "Mission District": 20,
            "Fisherman's Wharf": 10,
            "Russian Hill": 8,
            "North Beach": 11,
            "Chinatown": 15,
            "Pacific Heights": 7,
            "The Castro": 22,
            "Nob Hill": 12,
            "Sunset District": 19
        },
        "North Beach": {
            "Union Square": 7,
            "Mission District": 18,
            "Fisherman's Wharf": 5,
            "Russian Hill": 4,
            "Marina District": 9,
            "Chinatown": 6,
            "Pacific Heights": 8,
            "The Castro": 23,
            "Nob Hill": 7,
            "Sunset District": 27
        },
        "Chinatown": {
            "Union Square": 7,
            "Mission District": 17,
            "Fisherman's Wharf": 8,
            "Russian Hill": 7,
            "Marina District": 12,
            "North Beach": 3,
            "Pacific Heights": 10,
            "The Castro": 22,
            "Nob Hill": 9,
            "Sunset District": 29
        },
        "Pacific Heights": {
            "Union Square": 12,
            "Mission District": 15,
            "Fisherman's Wharf": 13,
            "Russian Hill": 7,
            "Marina District": 6,
            "North Beach": 9,
            "Chinatown": 11,
            "The Castro": 16,
            "Nob Hill": 8,
            "Sunset District": 21
        },
        "The Castro": {
            "Union Square": 19,
            "Mission District": 7,
            "Fisherman's Wharf": 24,
            "Russian Hill": 18,
            "Marina District": 21,
            "North Beach": 20,
            "Chinatown": 22,
            "Pacific Heights": 16,
            "Nob Hill": 16,
            "Sunset District": 17
        },
        "Nob Hill": {
            "Union Square": 7,
            "Mission District": 13,
            "Fisherman's Wharf": 10,
            "Russian Hill": 5,
            "Marina District": 11,
            "North Beach": 8,
            "Chinatown": 6,
            "Pacific Heights": 8,
            "The Castro": 17,
            "Sunset District": 24
        },
        "Sunset District": {
            "Union Square": 30,
            "Mission District": 25,
            "Fisherman's Wharf": 29,
            "Russian Hill": 24,
            "Marina District": 21,
            "North Beach": 28,
            "Chinatown": 30,
            "Pacific Heights": 21,
            "The Castro": 17,
            "Nob Hill": 27
        }
    }
    
    # Our day starts at Union Square at 9:00AM = 540 minutes.
    start_time = 540
    
    # Create the Z3 Optimize object.
    opt = Optimize()
    
    # Create decision variables.
    # For each friend, x_f is a boolean indicating if we schedule a meeting with friend f.
    # s_f is an integer for the start time of the meeting (if scheduled).
    s_vars = {}  # mapping friend name -> start time variable
    x_vars = {}  # mapping friend name -> Bool (True means meeting scheduled)
    
    for f in friends:
        name = f["name"]
        s_vars[name] = Int(f"s_{name}")
        x_vars[name] = Bool(f"meet_{name}")
        # If we meet friend f, then we require that the meeting start time lies within
        # the friend’s available window (and we account for the meeting’s duration)
        # Also, if it were the first meeting we must travel from Union Square.
        opt.add(Implies(x_vars[name],
                        And(
                            s_vars[name] >= f["avail_start"],
                            s_vars[name] <= f["avail_end"] - f["duration"],
                            s_vars[name] + f["duration"] <= f["avail_end"],
                            s_vars[name] >= start_time + travel["Union Square"][f["location"]]
                        )
                    ))
        # (If not scheduled, s_f can be arbitrary.)
    
    # For any two meetings that are scheduled, enforce a “no overlap” constraint,
    # taking travel time into account.
    # If meetings with friend i and friend j are both scheduled then either i happens before j or vice-versa.
    n = len(friends)
    friend_names = [f["name"] for f in friends]
    for i in range(n):
        for j in range(i + 1, n):
            name_i = friend_names[i]
            name_j = friend_names[j]
            # Retrieve the durations and locations from our friends list.
            dur_i = friends[i]["duration"]
            dur_j = friends[j]["duration"]
            loc_i = friends[i]["location"]
            loc_j = friends[j]["location"]
            travel_ij = travel[loc_i][loc_j]
            travel_ji = travel[loc_j][loc_i]
            # Impose the ordering if both meetings are to be scheduled.
            opt.add(Implies(And(x_vars[name_i], x_vars[name_j]),
                        Or(
                            s_vars[name_i] + dur_i + travel_ij <= s_vars[name_j],
                            s_vars[name_j] + dur_j + travel_ji <= s_vars[name_i]
                        )
                    ))
    
    # Our objective is to maximize the number of meetings scheduled.
    opt.maximize(Sum([If(x_vars[f["name"]], 1, 0) for f in friends]))
    
    # Solve the scheduling problem.
    if opt.check() == sat:
        model = opt.model()
        scheduled = []
        for f in friends:
            name = f["name"]
            if is_true(model.evaluate(x_vars[name], model_completion=True)):
                st = model.evaluate(s_vars[name]).as_long()
                scheduled.append((st, name, f["duration"]))
        # Sort the scheduled meetings by their start times.
        scheduled.sort(key=lambda tup: tup[0])
        
        itinerary = []
        for st, name, dur in scheduled:
            start_str = minutes_to_hhmm(st)
            end_str = minutes_to_hhmm(st + dur)
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": start_str,
                "end_time": end_str
            })
        
        # Output the itinerary as a JSON-formatted dictionary.
        print(json.dumps({"itinerary": itinerary}, indent=2))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()