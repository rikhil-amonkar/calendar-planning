#!/usr/bin/env python3
import json
from z3 import *

# Global travel times dictionary (in minutes)
travel_times = {
    "Marina District": {
        "Bayview": 27,
        "Sunset District": 19,
        "Richmond District": 11,
        "Nob Hill": 12,
        "Chinatown": 15,
        "Haight-Ashbury": 16,
        "North Beach": 11,
        "Russian Hill": 8,
        "Embarcadero": 14
    },
    "Bayview": {
        "Marina District": 27,
        "Sunset District": 23,
        "Richmond District": 25,
        "Nob Hill": 20,
        "Chinatown": 19,
        "Haight-Ashbury": 19,
        "North Beach": 22,
        "Russian Hill": 23,
        "Embarcadero": 19
    },
    "Sunset District": {
        "Marina District": 21,
        "Bayview": 22,
        "Richmond District": 12,
        "Nob Hill": 27,
        "Chinatown": 30,
        "Haight-Ashbury": 15,
        "North Beach": 28,
        "Russian Hill": 24,
        "Embarcadero": 30
    },
    "Richmond District": {
        "Marina District": 9,
        "Bayview": 27,
        "Sunset District": 11,
        "Nob Hill": 17,
        "Chinatown": 20,
        "Haight-Ashbury": 10,
        "North Beach": 17,
        "Russian Hill": 13,
        "Embarcadero": 19
    },
    "Nob Hill": {
        "Marina District": 11,
        "Bayview": 19,
        "Sunset District": 24,
        "Richmond District": 14,
        "Chinatown": 6,
        "Haight-Ashbury": 13,
        "North Beach": 8,
        "Russian Hill": 5,
        "Embarcadero": 9
    },
    "Chinatown": {
        "Marina District": 12,
        "Bayview": 20,
        "Sunset District": 29,
        "Richmond District": 20,
        "Nob Hill": 9,
        "Haight-Ashbury": 19,
        "North Beach": 3,
        "Russian Hill": 7,
        "Embarcadero": 5
    },
    "Haight-Ashbury": {
        "Marina District": 17,
        "Bayview": 18,
        "Sunset District": 15,
        "Richmond District": 10,
        "Nob Hill": 15,
        "Chinatown": 19,
        "North Beach": 19,
        "Russian Hill": 17,
        "Embarcadero": 20
    },
    "North Beach": {
        "Marina District": 9,
        "Bayview": 25,
        "Sunset District": 27,
        "Richmond District": 18,
        "Nob Hill": 7,
        "Chinatown": 6,
        "Haight-Ashbury": 18,
        "Russian Hill": 4,
        "Embarcadero": 6
    },
    "Russian Hill": {
        "Marina District": 7,
        "Bayview": 23,
        "Sunset District": 23,
        "Richmond District": 14,
        "Nob Hill": 5,
        "Chinatown": 9,
        "Haight-Ashbury": 17,
        "North Beach": 5,
        "Embarcadero": 8
    },
    "Embarcadero": {
        "Marina District": 12,
        "Bayview": 21,
        "Sunset District": 30,
        "Richmond District": 21,
        "Nob Hill": 10,
        "Chinatown": 7,
        "Haight-Ashbury": 21,
        "North Beach": 5,
        "Russian Hill": 8
    }
}

# Helper function to convert minutes since midnight to H:MM (24-hour) format.
def minutes_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours}:{minutes:02d}"

def main():
    # Friend meeting data with availability windows and minimum meeting durations (in minutes)
    friends = [
        {"name": "Charles",   "location": "Bayview",        "avail_start": 11*60 + 30, "avail_end": 14*60 + 30, "min_dur": 45},
        {"name": "Robert",    "location": "Sunset District","avail_start": 16*60 + 45, "avail_end": 21*60,      "min_dur": 30},
        {"name": "Karen",     "location": "Richmond District","avail_start": 19*60 + 15, "avail_end": 21*60 + 30, "min_dur": 60},
        {"name": "Rebecca",   "location": "Nob Hill",       "avail_start": 16*60 + 15, "avail_end": 20*60 + 30, "min_dur": 90},
        {"name": "Margaret",  "location": "Chinatown",      "avail_start": 14*60 + 15, "avail_end": 19*60 + 45, "min_dur": 120},
        {"name": "Patricia",  "location": "Haight-Ashbury", "avail_start": 14*60 + 30, "avail_end": 20*60 + 30, "min_dur": 45},
        {"name": "Mark",      "location": "North Beach",    "avail_start": 14*60,      "avail_end": 18*60 + 30, "min_dur": 105},
        {"name": "Melissa",   "location": "Russian Hill",   "avail_start": 13*60,      "avail_end": 19*60 + 45, "min_dur": 30},
        {"name": "Laura",     "location": "Embarcadero",    "avail_start": 7*60 + 45,  "avail_end": 13*60 + 15, "min_dur": 105}
    ]

    arrival_time = 9 * 60  # 9:00 AM in minutes
    base_location = "Marina District"
    num = len(friends)
    
    # Create an Optimize solver to maximize number of meetings
    opt = Optimize()

    # Decision variables:
    # For each friend, a boolean indicating if the meeting is scheduled,
    # an integer start time and end time of the meeting (in minutes since midnight).
    meets = [Bool(f"meet_{i}") for i in range(num)]
    starts = [Int(f"start_{i}") for i in range(num)]
    ends = [Int(f"end_{i}") for i in range(num)]

    # Add constraints for each meeting: time window and minimum duration if scheduled.
    for i, friend in enumerate(friends):
        # If meeting is scheduled then meeting must occur within the friend's availability window.
        opt.add(Implies(meets[i], starts[i] >= friend["avail_start"]))
        opt.add(Implies(meets[i], ends[i] <= friend["avail_end"]))
        opt.add(Implies(meets[i], ends[i] - starts[i] >= friend["min_dur"]))
        # If not scheduled, fix start and end times (arbitrary, here we fix them to 0).
        opt.add(Implies(Not(meets[i]), And(starts[i] == 0, ends[i] == 0)))
        # General time bounds (within the same day)
        opt.add(starts[i] >= 0, starts[i] <= 1440)
        opt.add(ends[i] >= 0, ends[i] <= 1440)

    # Enforce non-overlap and travel time constraints between any two scheduled meetings.
    for i in range(num):
        for j in range(i+1, num):
            # Only if both meetings are scheduled.
            loc_i = friends[i]["location"]
            loc_j = friends[j]["location"]
            travel_ij = travel_times[loc_i][loc_j]
            travel_ji = travel_times[loc_j][loc_i]
            # Either meeting i finishes and then after travel meeting j starts,
            # or meeting j finishes and then after travel meeting i starts.
            opt.add(Implies(And(meets[i], meets[j]),
                            Or(starts[j] >= ends[i] + travel_ij,
                               starts[i] >= ends[j] + travel_ji)))
    
    # Enforce that the earliest scheduled meeting is reachable from the base.
    # For each meeting, if it is scheduled and it is the earliest among scheduled meetings,
    # then its start time must be at least arrival_time plus travel time from the base location.
    for i in range(num):
        # Construct the "is_earliest" condition for meeting i:
        is_earliest = And([Or(Not(meets[j]), starts[i] <= starts[j]) for j in range(num) if j != i])
        opt.add(Implies(And(meets[i], is_earliest),
                        starts[i] >= arrival_time + travel_times[base_location][friends[i]["location"]]))
    
    # Objective: maximize the number of meetings scheduled.
    opt.maximize(Sum([If(meets[i], 1, 0) for i in range(num)]))
    
    # Check for satisfiability and extract a solution.
    if opt.check() == sat:
        model = opt.model()
        scheduled = []
        for i in range(num):
            if is_true(model.evaluate(meets[i])):
                s_val = model.evaluate(starts[i]).as_long()
                e_val = model.evaluate(ends[i]).as_long()
                scheduled.append({
                    "person": friends[i]["name"],
                    "location": friends[i]["location"],
                    "start": s_val,
                    "end": e_val
                })
        # Sort scheduled meetings by start time.
        scheduled.sort(key=lambda x: x["start"])
        itinerary = []
        for meeting in scheduled:
            itinerary.append({
                "action": "meet",
                "location": meeting["location"],
                "person": meeting["person"],
                "start_time": minutes_to_time(meeting["start"]),
                "end_time": minutes_to_time(meeting["end"])
            })
        output = {"itinerary": itinerary}
    else:
        output = {"itinerary": []}
    
    # Print the JSON output.
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()