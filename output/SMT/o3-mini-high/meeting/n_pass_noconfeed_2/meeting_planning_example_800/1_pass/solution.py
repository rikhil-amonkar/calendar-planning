from z3 import *
import json

def format_time(t):
    # Convert integer minutes to H:MM (24-hour format, no leading zero)
    hour = t // 60
    minute = t % 60
    return f"{hour}:{minute:02d}"

def main():
    # Travel times between locations (in minutes)
    # Keys are (from_location, to_location)
    travel_times = {
        ("Union Square", "The Castro"): 17,
        ("Union Square", "North Beach"): 10,
        ("Union Square", "Embarcadero"): 11,
        ("Union Square", "Alamo Square"): 15,
        ("Union Square", "Nob Hill"): 9,
        ("Union Square", "Presidio"): 24,
        ("Union Square", "Fisherman's Wharf"): 15,
        ("Union Square", "Mission District"): 14,
        ("Union Square", "Haight-Ashbury"): 18,
        ("The Castro", "Union Square"): 19,
        ("The Castro", "North Beach"): 20,
        ("The Castro", "Embarcadero"): 22,
        ("The Castro", "Alamo Square"): 8,
        ("The Castro", "Nob Hill"): 16,
        ("The Castro", "Presidio"): 20,
        ("The Castro", "Fisherman's Wharf"): 24,
        ("The Castro", "Mission District"): 7,
        ("The Castro", "Haight-Ashbury"): 6,
        ("North Beach", "Union Square"): 7,
        ("North Beach", "The Castro"): 23,
        ("North Beach", "Embarcadero"): 6,
        ("North Beach", "Alamo Square"): 16,
        ("North Beach", "Nob Hill"): 7,
        ("North Beach", "Presidio"): 17,
        ("North Beach", "Fisherman's Wharf"): 5,
        ("North Beach", "Mission District"): 18,
        ("North Beach", "Haight-Ashbury"): 18,
        ("Embarcadero", "Union Square"): 10,
        ("Embarcadero", "The Castro"): 25,
        ("Embarcadero", "North Beach"): 5,
        ("Embarcadero", "Alamo Square"): 19,
        ("Embarcadero", "Nob Hill"): 10,
        ("Embarcadero", "Presidio"): 20,
        ("Embarcadero", "Fisherman's Wharf"): 6,
        ("Embarcadero", "Mission District"): 20,
        ("Embarcadero", "Haight-Ashbury"): 21,
        ("Alamo Square", "Union Square"): 14,
        ("Alamo Square", "The Castro"): 8,
        ("Alamo Square", "North Beach"): 15,
        ("Alamo Square", "Embarcadero"): 16,
        ("Alamo Square", "Nob Hill"): 11,
        ("Alamo Square", "Presidio"): 17,
        ("Alamo Square", "Fisherman's Wharf"): 19,
        ("Alamo Square", "Mission District"): 10,
        ("Alamo Square", "Haight-Ashbury"): 5,
        ("Nob Hill", "Union Square"): 7,
        ("Nob Hill", "The Castro"): 17,
        ("Nob Hill", "North Beach"): 8,
        ("Nob Hill", "Embarcadero"): 9,
        ("Nob Hill", "Alamo Square"): 11,
        ("Nob Hill", "Presidio"): 17,
        ("Nob Hill", "Fisherman's Wharf"): 10,
        ("Nob Hill", "Mission District"): 13,
        ("Nob Hill", "Haight-Ashbury"): 13,
        ("Presidio", "Union Square"): 22,
        ("Presidio", "The Castro"): 21,
        ("Presidio", "North Beach"): 18,
        ("Presidio", "Embarcadero"): 20,
        ("Presidio", "Alamo Square"): 19,
        ("Presidio", "Nob Hill"): 18,
        ("Presidio", "Fisherman's Wharf"): 19,
        ("Presidio", "Mission District"): 26,
        ("Presidio", "Haight-Ashbury"): 15,
        ("Fisherman's Wharf", "Union Square"): 13,
        ("Fisherman's Wharf", "The Castro"): 27,
        ("Fisherman's Wharf", "North Beach"): 6,
        ("Fisherman's Wharf", "Embarcadero"): 8,
        ("Fisherman's Wharf", "Alamo Square"): 21,
        ("Fisherman's Wharf", "Nob Hill"): 11,
        ("Fisherman's Wharf", "Presidio"): 17,
        ("Fisherman's Wharf", "Mission District"): 22,
        ("Fisherman's Wharf", "Haight-Ashbury"): 22,
        ("Mission District", "Union Square"): 15,
        ("Mission District", "The Castro"): 7,
        ("Mission District", "North Beach"): 17,
        ("Mission District", "Embarcadero"): 19,
        ("Mission District", "Alamo Square"): 11,
        ("Mission District", "Nob Hill"): 12,
        ("Mission District", "Presidio"): 25,
        ("Mission District", "Fisherman's Wharf"): 22,
        ("Mission District", "Haight-Ashbury"): 12,
        ("Haight-Ashbury", "Union Square"): 19,
        ("Haight-Ashbury", "The Castro"): 6,
        ("Haight-Ashbury", "North Beach"): 19,
        ("Haight-Ashbury", "Embarcadero"): 20,
        ("Haight-Ashbury", "Alamo Square"): 5,
        ("Haight-Ashbury", "Nob Hill"): 15,
        ("Haight-Ashbury", "Presidio"): 15,
        ("Haight-Ashbury", "Fisherman's Wharf"): 23,
        ("Haight-Ashbury", "Mission District"): 11,
    }
    
    # Meetings data:
    # Each meeting has a person, location, availability window (in minutes from midnight), and minimum meeting duration.
    meetings = []
    meetings.append({
        "person": "Melissa",
        "location": "The Castro",
        "avail_start": 20 * 60 + 15,  # 20:15
        "avail_end": 21 * 60 + 15,    # 21:15
        "min_duration": 30
    })
    meetings.append({
        "person": "Kimberly",
        "location": "North Beach",
        "avail_start": 7 * 60,       # 7:00
        "avail_end": 10 * 60 + 30,    # 10:30
        "min_duration": 15
    })
    meetings.append({
        "person": "Joseph",
        "location": "Embarcadero",
        "avail_start": 15 * 60 + 30,  # 15:30
        "avail_end": 19 * 60 + 30,    # 19:30
        "min_duration": 75
    })
    meetings.append({
        "person": "Barbara",
        "location": "Alamo Square",
        "avail_start": 20 * 60 + 45,  # 20:45
        "avail_end": 21 * 60 + 45,    # 21:45
        "min_duration": 15
    })
    meetings.append({
        "person": "Kenneth",
        "location": "Nob Hill",
        "avail_start": 12 * 60 + 15,  # 12:15
        "avail_end": 17 * 60 + 15,    # 17:15
        "min_duration": 105
    })
    meetings.append({
        "person": "Joshua",
        "location": "Presidio",
        "avail_start": 16 * 60 + 30,  # 16:30
        "avail_end": 18 * 60 + 15,    # 18:15
        "min_duration": 105
    })
    meetings.append({
        "person": "Brian",
        "location": "Fisherman's Wharf",
        "avail_start": 9 * 60 + 30,   # 9:30
        "avail_end": 15 * 60 + 30,    # 15:30
        "min_duration": 45
    })
    meetings.append({
        "person": "Steven",
        "location": "Mission District",
        "avail_start": 19 * 60 + 30,  # 19:30
        "avail_end": 21 * 60,         # 21:00
        "min_duration": 90
    })
    meetings.append({
        "person": "Betty",
        "location": "Haight-Ashbury",
        "avail_start": 19 * 60,       # 19:00
        "avail_end": 20 * 60 + 30,    # 20:30
        "min_duration": 90
    })
    
    # Create an optimizer instance
    opt = Optimize()
    
    # For each meeting, create decision variables for start time (S), end time (E) and a boolean flag (selected)
    for m in meetings:
        m["S"] = Int(f"S_{m['person']}")
        m["E"] = Int(f"E_{m['person']}")
        m["selected"] = Bool(f"sel_{m['person']}")
        # If a meeting is selected, its start and end times must lie within its available window, and last at least the minimum duration.
        opt.add(Implies(m["selected"],
                        And(m["S"] >= m["avail_start"],
                            m["E"] <= m["avail_end"],
                            m["E"] - m["S"] >= m["min_duration"])))
        # Also, from the starting location Union Square at 9:00 (540 minutes), you must account for travel time.
        ts = travel_times[("Union Square", m["location"])]
        opt.add(Implies(m["selected"], m["S"] >= 540 + ts))
        # Ensure non-negativity when selected.
        opt.add(Implies(m["selected"], m["S"] >= 0))
        opt.add(Implies(m["selected"], m["E"] >= 0))
    
    # Add ordering constraints: For any two meetings that are selected, one must come before the other (with travel time accounted for).
    n = len(meetings)
    for i in range(n):
        for j in range(i + 1, n):
            mi = meetings[i]
            mj = meetings[j]
            travel_ij = travel_times[(mi["location"], mj["location"])]
            travel_ji = travel_times[(mj["location"], mi["location"])]
            # If both meetings are selected then either mi happens before mj or mj happens before mi.
            opt.add(Implies(And(mi["selected"], mj["selected"]),
                            Or(mi["E"] + travel_ij <= mj["S"],
                               mj["E"] + travel_ji <= mi["S"])))
    
    # Set the objective: maximize the number of meetings scheduled.
    opt.maximize(Sum([If(m["selected"], 1, 0) for m in meetings]))
    
    if opt.check() == sat:
        model = opt.model()
        scheduled = []
        for m in meetings:
            if is_true(model.evaluate(m["selected"])):
                S_val = model.evaluate(m["S"]).as_long()
                E_val = model.evaluate(m["E"]).as_long()
                scheduled.append({
                    "person": m["person"],
                    "location": m["location"],
                    "S": S_val,
                    "E": E_val
                })
        # Sort the scheduled meetings in order of their start times.
        scheduled.sort(key=lambda x: x["S"])
        itinerary = []
        for m in scheduled:
            itinerary.append({
                "action": "meet",
                "location": m["location"],
                "person": m["person"],
                "start_time": format_time(m["S"]),
                "end_time": format_time(m["E"])
            })
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()