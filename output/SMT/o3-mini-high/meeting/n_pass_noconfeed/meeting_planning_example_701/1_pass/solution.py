from z3 import *
import json

def minutes_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours}:{minutes:02d}"

def main():
    # Meeting data for each friend, with availability windows and minimum meeting durations.
    # Times are in minutes from midnight.
    meetings = [
        {"name": "Lisa", "location": "The Castro", "avail_start": 19*60+15, "avail_end": 21*60+15, "min_duration": 120},
        {"name": "Daniel", "location": "Nob Hill", "avail_start": 8*60+15,  "avail_end": 11*60,    "min_duration": 15},
        {"name": "Elizabeth", "location": "Presidio", "avail_start": 21*60+15, "avail_end": 22*60+15, "min_duration": 45},
        {"name": "Steven", "location": "Marina District", "avail_start": 16*60+30, "avail_end": 20*60+45, "min_duration": 90},
        {"name": "Timothy", "location": "Pacific Heights", "avail_start": 12*60, "avail_end": 18*60, "min_duration": 90},
        {"name": "Ashley", "location": "Golden Gate Park", "avail_start": 20*60+45, "avail_end": 21*60+45, "min_duration": 60},
        {"name": "Kevin", "location": "Chinatown", "avail_start": 12*60, "avail_end": 19*60, "min_duration": 30},
        {"name": "Betty", "location": "Richmond District", "avail_start": 13*60+15, "avail_end": 15*60+45, "min_duration": 30}
    ]
    
    # Travel times in minutes between locations.
    # Note: travel times are not necessarily symmetric.
    travel_time = {}
    # From Mission District
    travel_time[("Mission District", "The Castro")] = 7
    travel_time[("Mission District", "Nob Hill")] = 12
    travel_time[("Mission District", "Presidio")] = 25
    travel_time[("Mission District", "Marina District")] = 19
    travel_time[("Mission District", "Pacific Heights")] = 16
    travel_time[("Mission District", "Golden Gate Park")] = 17
    travel_time[("Mission District", "Chinatown")] = 16
    travel_time[("Mission District", "Richmond District")] = 20

    # From The Castro
    travel_time[("The Castro", "Mission District")] = 7
    travel_time[("The Castro", "Nob Hill")] = 16
    travel_time[("The Castro", "Presidio")] = 20
    travel_time[("The Castro", "Marina District")] = 21
    travel_time[("The Castro", "Pacific Heights")] = 16
    travel_time[("The Castro", "Golden Gate Park")] = 11
    travel_time[("The Castro", "Chinatown")] = 22
    travel_time[("The Castro", "Richmond District")] = 16

    # From Nob Hill
    travel_time[("Nob Hill", "Mission District")] = 13
    travel_time[("Nob Hill", "The Castro")] = 17
    travel_time[("Nob Hill", "Presidio")] = 17
    travel_time[("Nob Hill", "Marina District")] = 11
    travel_time[("Nob Hill", "Pacific Heights")] = 8
    travel_time[("Nob Hill", "Golden Gate Park")] = 17
    travel_time[("Nob Hill", "Chinatown")] = 6
    travel_time[("Nob Hill", "Richmond District")] = 14

    # From Presidio
    travel_time[("Presidio", "Mission District")] = 26
    travel_time[("Presidio", "The Castro")] = 21
    travel_time[("Presidio", "Nob Hill")] = 18
    travel_time[("Presidio", "Marina District")] = 11
    travel_time[("Presidio", "Pacific Heights")] = 11
    travel_time[("Presidio", "Golden Gate Park")] = 12
    travel_time[("Presidio", "Chinatown")] = 21
    travel_time[("Presidio", "Richmond District")] = 7

    # From Marina District
    travel_time[("Marina District", "Mission District")] = 20
    travel_time[("Marina District", "The Castro")] = 22
    travel_time[("Marina District", "Nob Hill")] = 12
    travel_time[("Marina District", "Presidio")] = 10
    travel_time[("Marina District", "Pacific Heights")] = 7
    travel_time[("Marina District", "Golden Gate Park")] = 18
    travel_time[("Marina District", "Chinatown")] = 15
    travel_time[("Marina District", "Richmond District")] = 11

    # From Pacific Heights
    travel_time[("Pacific Heights", "Mission District")] = 15
    travel_time[("Pacific Heights", "The Castro")] = 16
    travel_time[("Pacific Heights", "Nob Hill")] = 8
    travel_time[("Pacific Heights", "Presidio")] = 11
    travel_time[("Pacific Heights", "Marina District")] = 6
    travel_time[("Pacific Heights", "Golden Gate Park")] = 15
    travel_time[("Pacific Heights", "Chinatown")] = 11
    travel_time[("Pacific Heights", "Richmond District")] = 12

    # From Golden Gate Park
    travel_time[("Golden Gate Park", "Mission District")] = 17
    travel_time[("Golden Gate Park", "The Castro")] = 13
    travel_time[("Golden Gate Park", "Nob Hill")] = 20
    travel_time[("Golden Gate Park", "Presidio")] = 11
    travel_time[("Golden Gate Park", "Marina District")] = 16
    travel_time[("Golden Gate Park", "Pacific Heights")] = 16
    travel_time[("Golden Gate Park", "Chinatown")] = 23
    travel_time[("Golden Gate Park", "Richmond District")] = 7

    # From Chinatown
    travel_time[("Chinatown", "Mission District")] = 17
    travel_time[("Chinatown", "The Castro")] = 22
    travel_time[("Chinatown", "Nob Hill")] = 9
    travel_time[("Chinatown", "Presidio")] = 19
    travel_time[("Chinatown", "Marina District")] = 12
    travel_time[("Chinatown", "Pacific Heights")] = 10
    travel_time[("Chinatown", "Golden Gate Park")] = 23
    travel_time[("Chinatown", "Richmond District")] = 20

    # From Richmond District
    travel_time[("Richmond District", "Mission District")] = 20
    travel_time[("Richmond District", "The Castro")] = 16
    travel_time[("Richmond District", "Nob Hill")] = 17
    travel_time[("Richmond District", "Presidio")] = 7
    travel_time[("Richmond District", "Marina District")] = 9
    travel_time[("Richmond District", "Pacific Heights")] = 10
    travel_time[("Richmond District", "Golden Gate Park")] = 9
    travel_time[("Richmond District", "Chinatown")] = 20

    # Starting point: You arrive at Mission District at 9:00 (540 minutes from midnight)
    start_at = 540

    # Create an Optimize object
    opt = Optimize()

    n = len(meetings)
    meeting_vars = []  # List of tuples (start_i, end_i)
    attend_vars = []   # Boolean indicator for whether the meeting is attended

    for i in range(n):
        start_i = Int(f"start_{i}")
        end_i = Int(f"end_{i}")
        attend_i = Bool(f"attend_{i}")
        meeting_vars.append((start_i, end_i))
        attend_vars.append(attend_i)
        
        # If meeting is attended, the meeting must start no earlier than the participant's available start time...
        opt.add(Implies(attend_i, start_i >= meetings[i]["avail_start"]))
        # ...and end within the availability window (using the minimal meeting duration).
        opt.add(Implies(attend_i, start_i + meetings[i]["min_duration"] <= meetings[i]["avail_end"]))
        # Force the meeting duration to be exactly the minimum required if attended.
        opt.add(Implies(attend_i, end_i == start_i + meetings[i]["min_duration"]))
        # Additionally, if attended, you must be able to travel from Mission District to that location.
        loc = meetings[i]["location"]
        travel_from_start = travel_time[("Mission District", loc)]
        opt.add(Implies(attend_i, start_i >= start_at + travel_from_start))
    
    # For each pair of meetings, if both are attended, ensure that one meeting occurs after the other
    # with enough travel time between the locations.
    for i in range(n):
        for j in range(i+1, n):
            loc_i = meetings[i]["location"]
            loc_j = meetings[j]["location"]
            travel_ij = travel_time[(loc_i, loc_j)]
            travel_ji = travel_time[(loc_j, loc_i)]
            # Either meeting j starts after meeting i finishes plus travel time,
            # or meeting i starts after meeting j finishes plus travel time.
            opt.add(Implies(And(attend_vars[i], attend_vars[j]),
                            Or(meeting_vars[j][0] >= meeting_vars[i][1] + travel_ij,
                               meeting_vars[i][0] >= meeting_vars[j][1] + travel_ji)))
    
    # Objective: maximize the number of meetings attended.
    total_attended = Sum([If(attend_vars[i], 1, 0) for i in range(n)])
    opt.maximize(total_attended)
    
    if opt.check() == sat:
        model = opt.model()
        itinerary = []
        scheduled = []
        for i in range(n):
            if model.evaluate(attend_vars[i]):
                st = model.evaluate(meeting_vars[i][0]).as_long()
                et = model.evaluate(meeting_vars[i][1]).as_long()
                scheduled.append((st, i, et))
        # Sort the meetings by their start times for a clearer itinerary
        scheduled.sort(key=lambda x: x[0])
        for st, i, et in scheduled:
            itinerary.append({
                "action": "meet",
                "location": meetings[i]["location"],
                "person": meetings[i]["name"],
                "start_time": minutes_to_time(st),
                "end_time": minutes_to_time(et)
            })
        print(json.dumps({"itinerary": itinerary}))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()