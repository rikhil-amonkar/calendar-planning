from z3 import *
import json

def main():
    # Define meeting parameters (times in minutes from midnight)
    # 9:00 AM = 540 minutes
    persons = [
        {
            "name": "Karen",
            "location": "Nob Hill",
            "avail_start": 21 * 60 + 15,  # 21:15 -> 1275
            "avail_end": 21 * 60 + 45,    # 21:45 -> 1305
            "min_dur": 30
        },
        {
            "name": "Joseph",
            "location": "Haight-Ashbury",
            "avail_start": 12 * 60 + 30,  # 12:30 -> 750
            "avail_end": 19 * 60 + 45,    # 19:45 -> 1185
            "min_dur": 90
        },
        {
            "name": "Sandra",
            "location": "Chinatown",
            "avail_start": 7 * 60 + 15,   # 7:15 -> 435
            "avail_end": 19 * 60 + 15,    # 19:15 -> 1155
            "min_dur": 75
        },
        {
            "name": "Nancy",
            "location": "Marina District",
            "avail_start": 11 * 60,       # 11:00 -> 660
            "avail_end": 20 * 60 + 15,    # 20:15 -> 1215
            "min_dur": 105
        }
    ]
    
    # Travel times (in minutes)
    travel_times = {
        "Union Square": {
            "Nob Hill": 9,
            "Haight-Ashbury": 18,
            "Chinatown": 7,
            "Marina District": 18
        },
        "Nob Hill": {
            "Union Square": 7,
            "Haight-Ashbury": 13,
            "Chinatown": 6,
            "Marina District": 11
        },
        "Haight-Ashbury": {
            "Union Square": 17,
            "Nob Hill": 15,
            "Chinatown": 19,
            "Marina District": 17
        },
        "Chinatown": {
            "Union Square": 7,
            "Nob Hill": 8,
            "Haight-Ashbury": 19,
            "Marina District": 12
        },
        "Marina District": {
            "Union Square": 16,
            "Nob Hill": 12,
            "Haight-Ashbury": 16,
            "Chinatown": 16
        }
    }
    
    opt = Optimize()
    
    # Create decision variables for each meeting
    decisions = {}
    for person in persons:
        name = person["name"]
        s = Int('s_' + name)      # start time of the meeting
        order_var = Int('order_' + name)  # order of the meeting in the itinerary (0 if not attended)
        attend = Bool('attend_' + name)   # whether to attend this meeting
        decisions[name] = {
            "s": s,
            "order": order_var,
            "attend": attend,
            "location": person["location"],
            "avail_start": person["avail_start"],
            "avail_end": person["avail_end"],
            "min_dur": person["min_dur"]
        }
        # If meeting is attended, its start time must be no earlier than the availability start
        opt.add(Implies(attend, s >= person["avail_start"]))
        # Meeting must finish (s + min_dur) by availability end
        opt.add(Implies(attend, s + person["min_dur"] <= person["avail_end"]))
        # For attended meetings, order must be between 1 and the total number of meetings; if not attended, order is 0.
        opt.add(Implies(attend, And(order_var >= 1, order_var <= len(persons))))
        opt.add(Implies(Not(attend), order_var == 0))
        # Ensure start times are non-negative.
        opt.add(s >= 0)
    
    # Define overall finish time of the itinerary; it should be at least the end time of any attended meeting.
    T_last = Int('T_last')
    opt.add(T_last >= 540)  # cannot be before start of day (9:00 AM)
    for p in persons:
        name = p["name"]
        min_dur = p["min_dur"]
        opt.add(Implies(decisions[name]["attend"], T_last >= decisions[name]["s"] + min_dur))
    
    names = [p["name"] for p in persons]
    
    # Ensure that if two meetings are attended, they have distinct positions in the order.
    for i in range(len(names)):
        for j in range(i+1, len(names)):
            pi = decisions[names[i]]
            pj = decisions[names[j]]
            opt.add(Implies(And(pi["attend"], pj["attend"]), pi["order"] != pj["order"]))
    
    # For the first meeting in the schedule, incorporate the travel time from Union Square (which is the starting location at 9:00).
    for name in names:
        d = decisions[name]
        travel_from_start = travel_times["Union Square"][d["location"]]
        opt.add(Implies(And(d["attend"], d["order"] == 1), d["s"] >= 540 + travel_from_start))
    
    # For consecutive meetings, enforce that the start time of the later meeting is after the earlier meeting's end time plus travel time.
    for name_i in names:
        for name_j in names:
            if name_i != name_j:
                d_i = decisions[name_i]
                d_j = decisions[name_j]
                t_time = travel_times[d_i["location"]][d_j["location"]]
                # If meeting j immediately follows meeting i then:
                opt.add(Implies(And(d_i["attend"], d_j["attend"], d_j["order"] == d_i["order"] + 1),
                                d_j["s"] >= d_i["s"] + d_i["min_dur"] + t_time))
    
    # Enforce ordering consistency: if a meeting is assigned an order > 1, then some meeting must have the (order - 1).
    for k in range(2, len(persons) + 1):
        for name in names:
            d = decisions[name]
            opt.add(Implies(And(d["attend"], d["order"] == k),
                            Or([And(decisions[other]["attend"], decisions[other]["order"] == k - 1)
                                for other in names if other != name])))
    
    # Objective: maximize the number of meetings attended
    total_meetings = Sum([If(decisions[name]["attend"], 1, 0) for name in names])
    h1 = opt.maximize(total_meetings)
    # Secondary objective: minimize the finish time of the itinerary (T_last)
    h2 = opt.minimize(T_last)
    
    if opt.check() == sat:
        model = opt.model()
        itinerary = []
        attended_meetings = []
        for name in names:
            d = decisions[name]
            if is_true(model[d["attend"]]):
                order_val = model[d["order"]].as_long()
                start_time = model[d["s"]].as_long()
                end_time = start_time + d["min_dur"]
                attended_meetings.append((order_val, name, d["location"], start_time, end_time))
        attended_meetings.sort(key=lambda x: x[0])
        
        def format_time(minutes):
            h = minutes // 60
            m = minutes % 60
            return f"{h}:{m:02d}"
        
        itinerary_json = {"itinerary": []}
        for order_val, name, location, s_time, e_time in attended_meetings:
            itinerary_json["itinerary"].append({
                "action": "meet",
                "location": location,
                "person": name,
                "start_time": format_time(s_time),
                "end_time": format_time(e_time)
            })
        print(json.dumps(itinerary_json, indent=2))
    else:
        print(json.dumps({"itinerary": []}))
        
if __name__ == '__main__':
    main()