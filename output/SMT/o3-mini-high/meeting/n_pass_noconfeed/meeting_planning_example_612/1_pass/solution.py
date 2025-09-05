from z3 import *
import json

def minutes_to_time(m):
    hour = m // 60
    minute = m % 60
    return f"{hour}:{minute:02d}"

def main():
    # Define friend meeting data (times in minutes from midnight)
    # 9:00 -> 540 minutes, etc.
    friends = [
        {"name": "Emily", "location": "Russian Hill", "avail_start": 12*60+15, "avail_end": 14*60+15, "min_duration": 105},
        {"name": "Mark", "location": "Presidio", "avail_start": 14*60+45, "avail_end": 19*60+30, "min_duration": 60},
        {"name": "Deborah", "location": "Chinatown", "avail_start": 7*60+30, "avail_end": 15*60+30, "min_duration": 45},
        {"name": "Margaret", "location": "Sunset District", "avail_start": 21*60+30, "avail_end": 22*60+30, "min_duration": 60},
        {"name": "George", "location": "The Castro", "avail_start": 7*60+30, "avail_end": 14*60+15, "min_duration": 60},
        {"name": "Andrew", "location": "Embarcadero", "avail_start": 20*60+15, "avail_end": 22*60, "min_duration": 75},
        {"name": "Steven", "location": "Golden Gate Park", "avail_start": 11*60+15, "avail_end": 21*60+15, "min_duration": 105}
    ]
    n = len(friends)
    
    # Travel times dictionary (in minutes)
    travel_times = {
        ("Alamo Square", "Russian Hill"): 13,
        ("Alamo Square", "Presidio"): 18,
        ("Alamo Square", "Chinatown"): 16,
        ("Alamo Square", "Sunset District"): 16,
        ("Alamo Square", "The Castro"): 8,
        ("Alamo Square", "Embarcadero"): 17,
        ("Alamo Square", "Golden Gate Park"): 9,
        ("Russian Hill", "Alamo Square"): 15,
        ("Russian Hill", "Presidio"): 14,
        ("Russian Hill", "Chinatown"): 9,
        ("Russian Hill", "Sunset District"): 23,
        ("Russian Hill", "The Castro"): 21,
        ("Russian Hill", "Embarcadero"): 8,
        ("Russian Hill", "Golden Gate Park"): 21,
        ("Presidio", "Alamo Square"): 18,
        ("Presidio", "Russian Hill"): 14,
        ("Presidio", "Chinatown"): 21,
        ("Presidio", "Sunset District"): 15,
        ("Presidio", "The Castro"): 21,
        ("Presidio", "Embarcadero"): 20,
        ("Presidio", "Golden Gate Park"): 12,
        ("Chinatown", "Alamo Square"): 17,
        ("Chinatown", "Russian Hill"): 7,
        ("Chinatown", "Presidio"): 19,
        ("Chinatown", "Sunset District"): 29,
        ("Chinatown", "The Castro"): 22,
        ("Chinatown", "Embarcadero"): 5,
        ("Chinatown", "Golden Gate Park"): 23,
        ("Sunset District", "Alamo Square"): 17,
        ("Sunset District", "Russian Hill"): 24,
        ("Sunset District", "Presidio"): 16,
        ("Sunset District", "Chinatown"): 30,
        ("Sunset District", "The Castro"): 17,
        ("Sunset District", "Embarcadero"): 31,
        ("Sunset District", "Golden Gate Park"): 11,
        ("The Castro", "Alamo Square"): 8,
        ("The Castro", "Russian Hill"): 18,
        ("The Castro", "Presidio"): 20,
        ("The Castro", "Chinatown"): 20,
        ("The Castro", "Sunset District"): 17,
        ("The Castro", "Embarcadero"): 22,
        ("The Castro", "Golden Gate Park"): 11,
        ("Embarcadero", "Alamo Square"): 19,
        ("Embarcadero", "Russian Hill"): 8,
        ("Embarcadero", "Presidio"): 20,
        ("Embarcadero", "Chinatown"): 7,
        ("Embarcadero", "Sunset District"): 30,
        ("Embarcadero", "The Castro"): 25,
        ("Embarcadero", "Golden Gate Park"): 25,
        ("Golden Gate Park", "Alamo Square"): 10,
        ("Golden Gate Park", "Russian Hill"): 19,
        ("Golden Gate Park", "Presidio"): 11,
        ("Golden Gate Park", "Chinatown"): 23,
        ("Golden Gate Park", "Sunset District"): 10,
        ("Golden Gate Park", "The Castro"): 13,
        ("Golden Gate Park", "Embarcadero"): 25
    }
    
    # Create an Optimize object
    opt = Optimize()
    
    # Decision variables for each friend: 
    # pos: order in schedule (0 means not scheduled, positive integer means position),
    # start and finish times (in minutes from midnight)
    pos = [Int(f"pos_{i}") for i in range(n)]
    start = [Int(f"start_{i}") for i in range(n)]
    finish = [Int(f"finish_{i}") for i in range(n)]
    
    # General domain constraints for each meeting (if scheduled, pos > 0)
    for i in range(n):
        # pos is either 0 (unscheduled) or between 1 and n
        opt.add(pos[i] >= 0, pos[i] <= n)
        # Regardless, restrict start and finish in the day
        opt.add(start[i] >= 0, start[i] <= 1440)
        opt.add(finish[i] >= 0, finish[i] <= 1440)
        # If scheduled then meeting time must be within friend's available window
        opt.add(Implies(pos[i] > 0, start[i] >= friends[i]["avail_start"]))
        opt.add(Implies(pos[i] > 0, finish[i] <= friends[i]["avail_end"]))
        # If scheduled, meeting must have minimum duration and start before finish
        opt.add(Implies(pos[i] > 0, finish[i] - start[i] >= friends[i]["min_duration"]))
        opt.add(Implies(pos[i] > 0, start[i] < finish[i]))
    
    # For any two scheduled meetings, ensure they get distinct position numbers
    for i in range(n):
        for j in range(i+1, n):
            opt.add(Implies(And(pos[i] > 0, pos[j] > 0), pos[i] != pos[j]))
    
    # For the meeting that is first in the schedule (pos == 1), enforce travel from arrival location
    arrival_time = 540  # 9:00 AM
    for i in range(n):
        # travel from Alamo Square to meeting location
        t_time = travel_times[("Alamo Square", friends[i]["location"])]
        opt.add(Implies(pos[i] == 1, start[i] >= arrival_time + t_time))
    
    # For scheduled meetings (pos > 1), ensure there is a meeting that comes immediately before
    for i in range(n):
        # If meeting i is scheduled with order > 1, then there must be some meeting j with pos[j] = pos[i] - 1
        opt.add(Implies(pos[i] > 1, Or([pos[j] == pos[i] - 1 for j in range(n)])))
    
    # For every pair of meetings, if one comes immediately after the other, enforce travel time constraint
    for i in range(n):
        for j in range(n):
            if i != j:
                # If meeting i immediately follows meeting j, then meeting i must start after meeting j ends plus travel time.
                t_time = travel_times[(friends[j]["location"], friends[i]["location"])]
                opt.add(Implies(pos[i] == pos[j] + 1, start[i] >= finish[j] + t_time))
    
    # Objective: maximize the number of meetings scheduled
    total_meetings = Sum([If(pos[i] > 0, 1, 0) for i in range(n)])
    opt.maximize(total_meetings)
    
    # Check and get the optimal solution
    if opt.check() == sat:
        model = opt.model()
        scheduled = []
        for i in range(n):
            # Only include if pos value is positive (meeting scheduled)
            if model.evaluate(pos[i]).as_long() > 0:
                scheduled.append((model.evaluate(pos[i]).as_long(), i))
        # Sort scheduled meetings by their order (pos)
        scheduled.sort(key=lambda x: x[0])
        
        itinerary = []
        for order, i in scheduled:
            s_time = model.evaluate(start[i]).as_long()
            f_time = model.evaluate(finish[i]).as_long()
            itinerary.append({
                "action": "meet",
                "location": friends[i]["location"],
                "person": friends[i]["name"],
                "start_time": minutes_to_time(s_time),
                "end_time": minutes_to_time(f_time)
            })
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()