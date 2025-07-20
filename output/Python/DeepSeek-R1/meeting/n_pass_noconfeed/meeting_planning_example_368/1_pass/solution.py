# SOLUTION:
import itertools
import json

def min_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

travel_times = {
    "Bayview": {"Russian Hill": 23, "Alamo Square": 16, "North Beach": 21, "Financial District": 19},
    "Russian Hill": {"Bayview": 23, "Alamo Square": 15, "North Beach": 5, "Financial District": 11},
    "Alamo Square": {"Bayview": 16, "Russian Hill": 13, "North Beach": 15, "Financial District": 17},
    "North Beach": {"Bayview": 22, "Russian Hill": 4, "Alamo Square": 16, "Financial District": 8},
    "Financial District": {"Bayview": 19, "Russian Hill": 10, "Alamo Square": 17, "North Beach": 7}
}

friends = {
    "Joseph": {
        "location": "Russian Hill",
        "available_start": 8*60+30,   # 8:30 AM
        "available_end": 19*60+15,    # 7:15 PM
        "duration": 60
    },
    "Nancy": {
        "location": "Alamo Square",
        "available_start": 11*60,     # 11:00 AM
        "available_end": 16*60,       # 4:00 PM
        "duration": 90
    },
    "Jason": {
        "location": "North Beach",
        "available_start": 16*60+45, # 4:45 PM
        "available_end": 21*60+45,   # 9:45 PM
        "duration": 15
    },
    "Jeffrey": {
        "location": "Financial District",
        "available_start": 10*60+30, # 10:30 AM
        "available_end": 15*60+45,   # 3:45 PM
        "duration": 45
    }
}

all_friends = list(friends.keys())
best_schedule = None

for n in range(len(all_friends), 0, -1):
    found = False
    for subset in itertools.combinations(all_friends, n):
        for perm in itertools.permutations(subset):
            current_time = 540  # 9:00 AM in minutes
            current_location = "Bayview"
            schedule = []
            feasible = True
            for name in perm:
                loc = friends[name]["location"]
                travel = travel_times[current_location][loc]
                current_time += travel
                info = friends[name]
                start_meeting = max(current_time, info["available_start"])
                end_meeting = start_meeting + info["duration"]
                if end_meeting > info["available_end"]:
                    feasible = False
                    break
                schedule.append({
                    "friend": name,
                    "location": loc,
                    "start_time": start_meeting,
                    "end_time": end_meeting
                })
                current_time = end_meeting
                current_location = loc
            if feasible:
                best_schedule = schedule
                found = True
                break
        if found:
            break
    if found:
        break

itinerary = []
if best_schedule is not None:
    for meeting in best_schedule:
        itinerary.append({
            "action": "meet",
            "location": meeting["location"],
            "person": meeting["friend"],
            "start_time": min_to_time(meeting["start_time"]),
            "end_time": min_to_time(meeting["end_time"])
        })

print(json.dumps({"itinerary": itinerary}))