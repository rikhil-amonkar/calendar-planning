from z3 import *
import json

def main():
    # Define the meeting details for each friend.
    # Times are in minutes from midnight.
    friends = [
        {"name": "Emily", "location": "Russian Hill", "avail_start": 735, "avail_end": 855, "min_duration": 105},
        {"name": "Mark", "location": "Presidio", "avail_start": 885, "avail_end": 1170, "min_duration": 60},
        {"name": "Deborah", "location": "Chinatown", "avail_start": 450, "avail_end": 930, "min_duration": 45},
        {"name": "Margaret", "location": "Sunset District", "avail_start": 1290, "avail_end": 1350, "min_duration": 60},
        {"name": "George", "location": "The Castro", "avail_start": 450, "avail_end": 855, "min_duration": 60},
        {"name": "Andrew", "location": "Embarcadero", "avail_start": 1215, "avail_end": 1320, "min_duration": 75},
        {"name": "Steven", "location": "Golden Gate Park", "avail_start": 675, "avail_end": 1275, "min_duration": 105}
    ]
    
    # Travel times in minutes between locations.
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
    
    # You arrive at Alamo Square at 9:00 AM (540 minutes).
    arrival_time = 540

    num_friends = len(friends)
    opt = Optimize()

    # Decision variables:
    # For each friend i, s_i is the start time of the meeting, e_i is the end time, 
    # o_i is the order (position in the schedule, 0 if not attended), and attend_i is a boolean
    s = [Int(f"s_{i}") for i in range(num_friends)]
    e = [Int(f"e_{i}") for i in range(num_friends)]
    o = [Int(f"o_{i}") for i in range(num_friends)]
    attend = [Bool(f"attend_{i}") for i in range(num_friends)]

    # For each friend, add constraints if the meeting is attended.
    for i, friend in enumerate(friends):
        opt.add(
            If(
                attend[i],
                And(
                    s[i] >= friend["avail_start"],
                    s[i] <= friend["avail_end"] - friend["min_duration"],
                    e[i] <= friend["avail_end"],
                    e[i] >= friend["avail_start"] + friend["min_duration"],
                    e[i] - s[i] >= friend["min_duration"],
                    o[i] >= 1, o[i] <= num_friends
                ),
                And(s[i] == 0, e[i] == 0, o[i] == 0)
            )
        )
    
    # Ensure that if two meetings are attended, they have distinct order values.
    for i in range(num_friends):
        for j in range(i+1, num_friends):
            opt.add(Or(Not(And(attend[i], attend[j])), o[i] != o[j]))
    
    # The first meeting in the schedule must be reachable from Alamo Square.
    for i, friend in enumerate(friends):
        travel_from_start = travel_times.get(("Alamo Square", friend["location"]), 0)
        opt.add(
            If(And(attend[i], o[i] == 1),
               s[i] >= arrival_time + travel_from_start,
               True)
        )
    
    # For any two attended meetings, if meeting i comes before meeting j then
    # the start time of j must be at least the end time of i plus travel time.
    for i in range(num_friends):
        for j in range(num_friends):
            if i != j:
                travel_time_ij = travel_times.get((friends[i]["location"], friends[j]["location"]), 0)
                opt.add(
                    If(And(attend[i], attend[j], o[i] < o[j]),
                       s[j] >= e[i] + travel_time_ij,
                       True)
                )
    
    # Objective: maximize the number of meetings attended.
    total_attended = Sum([If(attend[i], 1, 0) for i in range(num_friends)])
    opt.maximize(total_attended)

    # Check for a solution.
    if opt.check() == sat:
        model = opt.model()
        schedule = []
        for i, friend in enumerate(friends):
            if is_true(model.evaluate(attend[i])):
                order_val = model.evaluate(o[i]).as_long()
                start_val = model.evaluate(s[i]).as_long()
                end_val = model.evaluate(e[i]).as_long()
                schedule.append((order_val, friend["name"], friend["location"], start_val, end_val))
        schedule.sort(key=lambda x: x[0])
        
        def format_time(t):
            hour = t // 60
            minute = t % 60
            return f"{hour}:{minute:02d}"
        
        itinerary = []
        for order_val, name, location, start_val, end_val in schedule:
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": name,
                "start_time": format_time(start_val),
                "end_time": format_time(end_val)
            })
        
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()