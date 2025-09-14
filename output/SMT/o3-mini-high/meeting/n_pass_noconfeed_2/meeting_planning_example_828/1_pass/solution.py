from z3 import *
import json

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

def main():
    # Define travel times (in minutes) between locations
    travel = {
        ("Marina District", "Richmond District"): 11,
        ("Marina District", "Union Square"): 16,
        ("Marina District", "Nob Hill"): 12,
        ("Marina District", "Fisherman's Wharf"): 10,
        ("Marina District", "Golden Gate Park"): 18,
        ("Marina District", "Embarcadero"): 14,
        ("Marina District", "Financial District"): 17,
        ("Marina District", "North Beach"): 11,
        ("Marina District", "Presidio"): 10,

        ("Richmond District", "Marina District"): 9,
        ("Richmond District", "Union Square"): 21,
        ("Richmond District", "Nob Hill"): 17,
        ("Richmond District", "Fisherman's Wharf"): 18,
        ("Richmond District", "Golden Gate Park"): 9,
        ("Richmond District", "Embarcadero"): 19,
        ("Richmond District", "Financial District"): 22,
        ("Richmond District", "North Beach"): 17,
        ("Richmond District", "Presidio"): 7,

        ("Union Square", "Marina District"): 18,
        ("Union Square", "Richmond District"): 20,
        ("Union Square", "Nob Hill"): 9,
        ("Union Square", "Fisherman's Wharf"): 15,
        ("Union Square", "Golden Gate Park"): 22,
        ("Union Square", "Embarcadero"): 11,
        ("Union Square", "Financial District"): 9,
        ("Union Square", "North Beach"): 10,
        ("Union Square", "Presidio"): 24,

        ("Nob Hill", "Marina District"): 11,
        ("Nob Hill", "Richmond District"): 14,
        ("Nob Hill", "Union Square"): 7,
        ("Nob Hill", "Fisherman's Wharf"): 10,
        ("Nob Hill", "Golden Gate Park"): 17,
        ("Nob Hill", "Embarcadero"): 9,
        ("Nob Hill", "Financial District"): 9,
        ("Nob Hill", "North Beach"): 8,
        ("Nob Hill", "Presidio"): 17,

        ("Fisherman's Wharf", "Marina District"): 9,
        ("Fisherman's Wharf", "Richmond District"): 18,
        ("Fisherman's Wharf", "Union Square"): 13,
        ("Fisherman's Wharf", "Nob Hill"): 11,
        ("Fisherman's Wharf", "Golden Gate Park"): 25,
        ("Fisherman's Wharf", "Embarcadero"): 8,
        ("Fisherman's Wharf", "Financial District"): 11,
        ("Fisherman's Wharf", "North Beach"): 6,
        ("Fisherman's Wharf", "Presidio"): 17,

        ("Golden Gate Park", "Marina District"): 16,
        ("Golden Gate Park", "Richmond District"): 7,
        ("Golden Gate Park", "Union Square"): 22,
        ("Golden Gate Park", "Nob Hill"): 20,
        ("Golden Gate Park", "Fisherman's Wharf"): 24,
        ("Golden Gate Park", "Embarcadero"): 25,
        ("Golden Gate Park", "Financial District"): 26,
        ("Golden Gate Park", "North Beach"): 23,
        ("Golden Gate Park", "Presidio"): 11,

        ("Embarcadero", "Marina District"): 12,
        ("Embarcadero", "Richmond District"): 21,
        ("Embarcadero", "Union Square"): 10,
        ("Embarcadero", "Nob Hill"): 10,
        ("Embarcadero", "Fisherman's Wharf"): 6,
        ("Embarcadero", "Golden Gate Park"): 25,
        ("Embarcadero", "Financial District"): 5,
        ("Embarcadero", "North Beach"): 5,
        ("Embarcadero", "Presidio"): 20,

        ("Financial District", "Marina District"): 15,
        ("Financial District", "Richmond District"): 21,
        ("Financial District", "Union Square"): 9,
        ("Financial District", "Nob Hill"): 8,
        ("Financial District", "Fisherman's Wharf"): 10,
        ("Financial District", "Golden Gate Park"): 23,
        ("Financial District", "Embarcadero"): 4,
        ("Financial District", "North Beach"): 7,
        ("Financial District", "Presidio"): 22,

        ("North Beach", "Marina District"): 9,
        ("North Beach", "Richmond District"): 18,
        ("North Beach", "Union Square"): 7,
        ("North Beach", "Nob Hill"): 7,
        ("North Beach", "Fisherman's Wharf"): 5,
        ("North Beach", "Golden Gate Park"): 22,
        ("North Beach", "Embarcadero"): 6,
        ("North Beach", "Financial District"): 8,
        ("North Beach", "Presidio"): 17,

        ("Presidio", "Marina District"): 11,
        ("Presidio", "Richmond District"): 7,
        ("Presidio", "Union Square"): 22,
        ("Presidio", "Nob Hill"): 18,
        ("Presidio", "Fisherman's Wharf"): 19,
        ("Presidio", "Golden Gate Park"): 12,
        ("Presidio", "Embarcadero"): 20,
        ("Presidio", "Financial District"): 23,
        ("Presidio", "North Beach"): 18,
    }

    # Meeting data: Each friend has a location, available time window (in minutes from midnight)
    # and a minimum meeting duration (in minutes). You arrive at Marina District at 9:00 (540).
    meetings = [
        {"person": "Stephanie", "location": "Richmond District",  "avail_start": 975,  "avail_end": 1290, "min_duration": 75},
        {"person": "William",   "location": "Union Square",      "avail_start": 645,  "avail_end": 1050, "min_duration": 45},
        {"person": "Elizabeth", "location": "Nob Hill",          "avail_start": 735,  "avail_end": 900,  "min_duration": 105},
        {"person": "Joseph",    "location": "Fisherman's Wharf", "avail_start": 765,  "avail_end": 840,  "min_duration": 75},
        {"person": "Anthony",   "location": "Golden Gate Park",  "avail_start": 780,  "avail_end": 1230, "min_duration": 75},
        {"person": "Barbara",   "location": "Embarcadero",       "avail_start": 1155, "avail_end": 1230, "min_duration": 75},
        {"person": "Carol",     "location": "Financial District","avail_start": 705,  "avail_end": 975,  "min_duration": 60},
        {"person": "Sandra",    "location": "North Beach",       "avail_start": 600,  "avail_end": 750,  "min_duration": 15},
        {"person": "Kenneth",   "location": "Presidio",          "avail_start": 1275, "avail_end": 1335, "min_duration": 45},
    ]

    n = len(meetings)
    opt = Optimize()
    
    # Create decision variables:
    # start_vars[i]: meeting start time for meeting i (in minutes from midnight)
    # sch_vars[i]: Boolean flag indicating whether meeting i is scheduled
    start_vars = [Int(f"start_{i}") for i in range(n)]
    sch_vars = [Bool(f"sch_{i}") for i in range(n)]
    
    # Add constraints for each meeting if it is scheduled.
    for i, m_data in enumerate(meetings):
        avail_start = m_data["avail_start"]
        avail_end = m_data["avail_end"]
        dur = m_data["min_duration"]
        loc = m_data["location"]
        # You arrive at Marina District at 9:00 (540); add travel time from Marina District.
        opt.add(Implies(sch_vars[i],
                        And(start_vars[i] >= avail_start,
                            start_vars[i] + dur <= avail_end,
                            start_vars[i] >= 540 + travel[("Marina District", loc)])))
    
    # Add disjunctive constraints for each pair of scheduled meetings
    # to ensure that, after including travel time between locations,
    # the meetings do not overlap.
    for i in range(n):
        for j in range(i+1, n):
            loc_i = meetings[i]["location"]
            loc_j = meetings[j]["location"]
            dur_i = meetings[i]["min_duration"]
            dur_j = meetings[j]["min_duration"]
            t_ij = travel[(loc_i, loc_j)]
            t_ji = travel[(loc_j, loc_i)]
            opt.add(Implies(And(sch_vars[i], sch_vars[j]),
                            Or(start_vars[i] + dur_i + t_ij <= start_vars[j],
                               start_vars[j] + dur_j + t_ji <= start_vars[i])))
    
    # Objective: maximize the number of scheduled meetings
    opt.maximize(Sum([If(s, 1, 0) for s in sch_vars]))
    
    if opt.check() == sat:
        model = opt.model()
        scheduled_meetings = []
        for i in range(n):
            if is_true(model.evaluate(sch_vars[i])):
                s_time = model.evaluate(start_vars[i]).as_long()
                e_time = s_time + meetings[i]["min_duration"]
                scheduled_meetings.append((s_time, {
                    "action": "meet",
                    "location": meetings[i]["location"],
                    "person": meetings[i]["person"],
                    "start_time": minutes_to_time(s_time),
                    "end_time": minutes_to_time(e_time)
                }))
        # Sort the scheduled meetings by start time
        scheduled_meetings.sort(key=lambda x: x[0])
        itinerary = [entry for (_, entry) in scheduled_meetings]
        print(json.dumps({"itinerary": itinerary}))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == '__main__':
    main()