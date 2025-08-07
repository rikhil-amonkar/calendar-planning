import itertools
from z3 import *
import json

def main():
    friends = {
        "Nancy": {"location": "Chinatown", "avail_start": 30, "avail_end": 270, "min_duration": 90},
        "Mary": {"location": "Alamo Square", "avail_start": 0, "avail_end": 720, "min_duration": 75},
        "Jessica": {"location": "Bayview", "avail_start": 135, "avail_end": 285, "min_duration": 45}
    }
    
    travel_times = {
        ("Financial District", "Chinatown"): 5,
        ("Financial District", "Alamo Square"): 17,
        ("Financial District", "Bayview"): 19,
        ("Chinatown", "Alamo Square"): 17,
        ("Chinatown", "Bayview"): 22,
        ("Alamo Square", "Chinatown"): 16,
        ("Alamo Square", "Bayview"): 16,
        ("Bayview", "Chinatown"): 18,
        ("Bayview", "Alamo Square"): 16
    }
    
    perms = list(itertools.permutations(friends.keys()))
    s = Solver()
    schedule = None
    
    for order in perms:
        start_vars = {friend: Int(f'start_{friend}') for friend in friends}
        constraints = []
        
        first = order[0]
        tt0 = travel_times[("Financial District", friends[first]["location"])]
        constraints.append(start_vars[first] >= tt0)
        constraints.append(start_vars[first] >= friends[first]["avail_start"])
        constraints.append(start_vars[first] + friends[first]["min_duration"] <= friends[first]["avail_end"])
        
        for idx in range(1, len(order)):
            prev = order[idx-1]
            curr = order[idx]
            tt = travel_times[(friends[prev]["location"], friends[curr]["location"])]
            constraints.append(start_vars[curr] >= start_vars[prev] + friends[prev]["min_duration"] + tt)
            constraints.append(start_vars[curr] >= friends[curr]["avail_start"])
            constraints.append(start_vars[curr] + friends[curr]["min_duration"] <= friends[curr]["avail_end"])
        
        s.push()
        s.add(constraints)
        if s.check() == sat:
            m = s.model()
            schedule = []
            for friend in order:
                start_val = m[start_vars[friend]].as_long()
                hours = 9 + start_val // 60
                minutes = start_val % 60
                start_time = f"{hours:02d}:{minutes:02d}"
                end_val = start_val + friends[friend]["min_duration"]
                hours_end = 9 + end_val // 60
                minutes_end = end_val % 60
                end_time = f"{hours_end:02d}:{minutes_end:02d}"
                schedule.append({"action": "meet", "person": friend, "start_time": start_time, "end_time": end_time})
            break
        else:
            s.pop()
    
    if schedule is None:
        schedule = []
    
    print("SOLUTION:")
    print(json.dumps({"itinerary": schedule}))

if __name__ == "__main__":
    main()