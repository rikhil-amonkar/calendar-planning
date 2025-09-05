import json
from z3 import *

def minutes_to_time_str(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

def main():
    # Travel times (in minutes) between locations.
    travel_times = {
        "Nob Hill": {
            "Embarcadero": 9,
            "The Castro": 17,
            "Haight-Ashbury": 13,
            "Union Square": 7,
            "North Beach": 8,
            "Pacific Heights": 8,
            "Chinatown": 6,
            "Golden Gate Park": 17,
            "Marina District": 11,
            "Russian Hill": 5
        },
        "Embarcadero": {
            "Nob Hill": 10,
            "The Castro": 25,
            "Haight-Ashbury": 21,
            "Union Square": 10,
            "North Beach": 5,
            "Pacific Heights": 11,
            "Chinatown": 7,
            "Golden Gate Park": 25,
            "Marina District": 12,
            "Russian Hill": 8
        },
        "The Castro": {
            "Nob Hill": 16,
            "Embarcadero": 22,
            "Haight-Ashbury": 6,
            "Union Square": 19,
            "North Beach": 20,
            "Pacific Heights": 16,
            "Chinatown": 22,
            "Golden Gate Park": 11,
            "Marina District": 21,
            "Russian Hill": 18
        },
        "Haight-Ashbury": {
            "Nob Hill": 15,
            "Embarcadero": 20,
            "The Castro": 6,
            "Union Square": 19,
            "North Beach": 19,
            "Pacific Heights": 12,
            "Chinatown": 19,
            "Golden Gate Park": 7,
            "Marina District": 17,
            "Russian Hill": 17
        },
        "Union Square": {
            "Nob Hill": 9,
            "Embarcadero": 11,
            "The Castro": 17,
            "Haight-Ashbury": 18,
            "North Beach": 10,
            "Pacific Heights": 15,
            "Chinatown": 7,
            "Golden Gate Park": 22,
            "Marina District": 18,
            "Russian Hill": 13
        },
        "North Beach": {
            "Nob Hill": 7,
            "Embarcadero": 6,
            "The Castro": 23,
            "Haight-Ashbury": 18,
            "Union Square": 7,
            "Pacific Heights": 8,
            "Chinatown": 6,
            "Golden Gate Park": 22,
            "Marina District": 9,
            "Russian Hill": 4
        },
        "Pacific Heights": {
            "Nob Hill": 8,
            "Embarcadero": 10,
            "The Castro": 16,
            "Haight-Ashbury": 11,
            "Union Square": 12,
            "North Beach": 9,
            "Chinatown": 11,
            "Golden Gate Park": 15,
            "Marina District": 6,
            "Russian Hill": 7
        },
        "Chinatown": {
            "Nob Hill": 9,
            "Embarcadero": 5,
            "The Castro": 22,
            "Haight-Ashbury": 19,
            "Union Square": 7,
            "North Beach": 3,
            "Pacific Heights": 10,
            "Golden Gate Park": 23,
            "Marina District": 12,
            "Russian Hill": 7
        },
        "Golden Gate Park": {
            "Nob Hill": 20,
            "Embarcadero": 25,
            "The Castro": 13,
            "Haight-Ashbury": 7,
            "Union Square": 22,
            "North Beach": 23,
            "Pacific Heights": 16,
            "Chinatown": 23,
            "Marina District": 16,
            "Russian Hill": 19
        },
        "Marina District": {
            "Nob Hill": 12,
            "Embarcadero": 14,
            "The Castro": 22,
            "Haight-Ashbury": 16,
            "Union Square": 16,
            "North Beach": 11,
            "Pacific Heights": 7,
            "Chinatown": 15,
            "Golden Gate Park": 18,
            "Russian Hill": 8
        },
        "Russian Hill": {
            "Nob Hill": 5,
            "Embarcadero": 8,
            "The Castro": 21,
            "Haight-Ashbury": 17,
            "Union Square": 10,
            "North Beach": 5,
            "Pacific Heights": 7,
            "Chinatown": 9,
            "Golden Gate Park": 21,
            "Marina District": 7
        }
    }
    
    # Friend meeting details.
    # Times are measured in minutes from midnight.
    friends = [
        {"name": "Mary", "location": "Embarcadero", "avail_start": 1200, "avail_end": 1275, "duration": 75},
        {"name": "Kenneth", "location": "The Castro", "avail_start": 675,  "avail_end": 1155, "duration": 30},
        {"name": "Joseph", "location": "Haight-Ashbury", "avail_start": 1200, "avail_end": 1320, "duration": 120},
        {"name": "Sarah", "location": "Union Square", "avail_start": 705,  "avail_end": 870,  "duration": 90},
        {"name": "Thomas", "location": "North Beach", "avail_start": 1155, "avail_end": 1185, "duration": 15},
        {"name": "Daniel", "location": "Pacific Heights", "avail_start": 825,  "avail_end": 1230, "duration": 15},
        {"name": "Richard", "location": "Chinatown", "avail_start": 480,  "avail_end": 1125, "duration": 30},
        {"name": "Mark", "location": "Golden Gate Park", "avail_start": 1050, "avail_end": 1290, "duration": 120},
        {"name": "David", "location": "Marina District", "avail_start": 1200, "avail_end": 1260, "duration": 60},
        {"name": "Karen", "location": "Russian Hill", "avail_start": 795,  "avail_end": 1110, "duration": 120}
    ]
    
    N = len(friends)
    opt = Optimize()

    # Decision variables for each friend:
    # scheduled[i] indicates whether meeting with friend i is scheduled.
    # order[i] is an integer representing the order in the itinerary (0 if not scheduled).
    # start[i] is the meeting start time (in minutes from midnight) if scheduled.
    scheduled = [Bool(f"scheduled_{i}") for i in range(N)]
    order = [Int(f"order_{i}") for i in range(N)]
    start = [Int(f"start_{i}") for i in range(N)]
    
    for i, f in enumerate(friends):
        # If scheduled then order is between 1 and N, else order must be 0.
        opt.add(Implies(scheduled[i], And(order[i] >= 1, order[i] <= N)))
        opt.add(Implies(Not(scheduled[i]), order[i] == 0))
        # Meeting must start no earlier than the friend's available start and finish by avail_end.
        opt.add(Implies(scheduled[i], start[i] >= f["avail_start"]))
        opt.add(Implies(scheduled[i], start[i] + f["duration"] <= f["avail_end"]))
        # Keep start time in a reasonable range.
        opt.add(Implies(scheduled[i], And(start[i] >= 0, start[i] < 1440)))
    
    # Enforce distinct ordering for scheduled meetings.
    for i in range(N):
        for j in range(i+1, N):
            opt.add(Implies(And(scheduled[i], scheduled[j]), order[i] != order[j]))
    
    # For the first meeting in the schedule, ensure we respect travel time from Nob Hill.
    for i, f in enumerate(friends):
        travel_from_nobhill = travel_times["Nob Hill"][f["location"]]
        opt.add(Implies(And(scheduled[i], order[i] == 1), start[i] >= 540 + travel_from_nobhill))
    
    # For any two scheduled meetings, if one comes before the other, then the start time of
    # the later meeting must be at least the finish time of the earlier meeting plus travel time.
    for i in range(N):
        for j in range(N):
            if i != j:
                t_ij = travel_times[friends[i]["location"]][friends[j]["location"]]
                opt.add(Implies(And(scheduled[i], scheduled[j], order[i] < order[j]),
                                start[j] >= start[i] + friends[i]["duration"] + t_ij))
    
    # Objective: maximize the number of meetings scheduled.
    opt.maximize(Sum([If(scheduled[i], 1, 0) for i in range(N)]))
    
    if opt.check() == sat:
        model = opt.model()
        itinerary_list = []
        scheduled_meetings = []
        for i, f in enumerate(friends):
            if model.evaluate(scheduled[i]):
                ord_val = model.evaluate(order[i]).as_long()
                start_val = model.evaluate(start[i]).as_long()
                end_val = start_val + f["duration"]
                scheduled_meetings.append({
                    "person": f["name"],
                    "location": f["location"],
                    "order": ord_val,
                    "start": start_val,
                    "end": end_val
                })
        # Sort meetings by their order in the itinerary.
        scheduled_meetings.sort(key=lambda x: x["order"])
        for meeting in scheduled_meetings:
            itinerary_list.append({
                "action": "meet",
                "location": meeting["location"],
                "person": meeting["person"],
                "start_time": minutes_to_time_str(meeting["start"]),
                "end_time": minutes_to_time_str(meeting["end"])
            })
        result = {"itinerary": itinerary_list}
        print(json.dumps(result, indent=2))
    else:
        print(json.dumps({"itinerary": []}, indent=2))
        
if __name__ == "__main__":
    main()