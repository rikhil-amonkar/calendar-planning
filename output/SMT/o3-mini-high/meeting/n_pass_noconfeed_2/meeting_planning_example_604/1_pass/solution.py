from z3 import *
import json

def minutes_to_time_str(m):
    # Convert minutes past midnight to a string "H:MM"
    h = m // 60
    minute = m % 60
    return f"{h}:{minute:02d}"

def main():
    # Friend meeting info: availability times in minutes from midnight and minimum meeting duration in minutes.
    friends = {
        "Laura": {
            "location": "The Castro",
            "window_start": 19 * 60 + 45,  # 19:45 -> 1185
            "window_end": 21 * 60 + 30,      # 21:30 -> 1290
            "min_dur": 105
        },
        "Daniel": {
            "location": "Golden Gate Park",
            "window_start": 21 * 60 + 15,  # 21:15 -> 1275
            "window_end": 21 * 60 + 45,      # 21:45 -> 1305
            "min_dur": 15
        },
        "William": {
            "location": "Embarcadero",
            "window_start": 7 * 60,   # 7:00 -> 420
            "window_end": 9 * 60,     # 9:00 -> 540
            "min_dur": 90
        },
        "Karen": {
            "location": "Russian Hill",
            "window_start": 14 * 60 + 30,  # 14:30 -> 870
            "window_end": 19 * 60 + 45,      # 19:45 -> 1185
            "min_dur": 30
        },
        "Stephanie": {
            "location": "Nob Hill",
            "window_start": 7 * 60 + 30,   # 7:30 -> 450
            "window_end": 9 * 60 + 30,       # 9:30 -> 570
            "min_dur": 45
        },
        "Joseph": {
            "location": "Alamo Square",
            "window_start": 11 * 60 + 30,  # 11:30 -> 690
            "window_end": 12 * 60 + 45,      # 12:45 -> 765
            "min_dur": 15
        },
        "Kimberly": {
            "location": "North Beach",
            "window_start": 15 * 60 + 45,  # 15:45 -> 945
            "window_end": 19 * 60 + 15,      # 19:15 -> 1155
            "min_dur": 30
        }
    }
    
    # Starting point: Fisherman's Wharf at 9:00 AM (9*60 = 540 minutes)
    start_time = 9 * 60  # 540 minutes
    
    # Travel times between locations (in minutes).
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
        ("North Beach", "Alamo Square"): 16
    }
    
    # Create an Optimize object
    opt = Optimize()
    
    # Decision variables: for each friend, whether to meet (x), and meeting start (s) and end (e) times.
    x = {}
    s_vars = {}
    e_vars = {}
    
    for person, info in friends.items():
        x[person] = Bool("x_" + person)
        s_vars[person] = Int("s_" + person)
        e_vars[person] = Int("e_" + person)
        
        # If a meeting is not scheduled, fix its time variables to 0.
        opt.add(Implies(Not(x[person]), s_vars[person] == 0))
        opt.add(Implies(Not(x[person]), e_vars[person] == 0))
        
        # If scheduled, the meeting must satisfy: 
        # start time >= max(friend's window start, travel time from Fisherman's Wharf)
        travel_from_start = travel_times[("Fisherman's Wharf", info["location"])]
        lower_bound = If(info["window_start"] > start_time + travel_from_start,
                         info["window_start"],
                         start_time + travel_from_start)
        opt.add(Implies(x[person], s_vars[person] >= lower_bound))
        # Meeting must finish by the friend's available window
        opt.add(Implies(x[person], e_vars[person] <= info["window_end"]))
        # The meeting must last at least the minimum required duration.
        opt.add(Implies(x[person], e_vars[person] - s_vars[person] >= info["min_dur"]))
        # Basic bounds for s and e (within a day)
        opt.add(s_vars[person] >= 0, s_vars[person] <= 1440)
        opt.add(e_vars[person] >= 0, e_vars[person] <= 1440)
    
    # Add ordering constraints between every pair of scheduled meetings.
    persons = list(friends.keys())
    for i in range(len(persons)):
        for j in range(i + 1, len(persons)):
            p1 = persons[i]
            p2 = persons[j]
            # Compute travel time from meeting p1 to p2 and vice versa.
            travel_p1_p2 = travel_times[(friends[p1]["location"], friends[p2]["location"])]
            travel_p2_p1 = travel_times[(friends[p2]["location"], friends[p1]["location"])]
            # If both meetings are scheduled, then either p1 comes before p2 or vice versa.
            opt.add(Implies(And(x[p1], x[p2]),
                            Or(e_vars[p1] + travel_p1_p2 <= s_vars[p2],
                               e_vars[p2] + travel_p2_p1 <= s_vars[p1])))
    
    # Objective: maximize the number of meetings scheduled.
    total_meetings = Sum([If(x[p], 1, 0) for p in persons])
    opt.maximize(total_meetings)
    
    if opt.check() == sat:
        model = opt.model()
        scheduled_meetings = []
        for person in persons:
            if is_true(model.evaluate(x[person])):
                start_val = model.evaluate(s_vars[person]).as_long()
                end_val = model.evaluate(e_vars[person]).as_long()
                scheduled_meetings.append((start_val, {
                    "action": "meet",
                    "location": friends[person]["location"],
                    "person": person,
                    "start_time": minutes_to_time_str(start_val),
                    "end_time": minutes_to_time_str(end_val)
                }))
        # Order the meetings by start time.
        scheduled_meetings.sort(key=lambda x: x[0])
        itinerary = [meeting for _, meeting in scheduled_meetings]
        print(json.dumps({"itinerary": itinerary}, indent=2))
    else:
        print(json.dumps({"itinerary": []}, indent=2))

if __name__ == "__main__":
    main()