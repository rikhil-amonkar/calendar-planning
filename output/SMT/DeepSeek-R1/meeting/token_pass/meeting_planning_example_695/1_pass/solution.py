from z3 import *
import json

def main():
    # Travel times in minutes between locations
    travel_times = {
        "Bayview": {
            "Nob Hill": 20,
            "Union Square": 17,
            "Chinatown": 18,
            "The Castro": 20,
            "Presidio": 31,
            "Pacific Heights": 23,
            "Russian Hill": 23
        },
        "Nob Hill": {
            "Bayview": 19,
            "Union Square": 7,
            "Chinatown": 6,
            "The Castro": 17,
            "Presidio": 17,
            "Pacific Heights": 8,
            "Russian Hill": 5
        },
        "Union Square": {
            "Bayview": 15,
            "Nob Hill": 9,
            "Chinatown": 7,
            "The Castro": 19,
            "Presidio": 24,
            "Pacific Heights": 15,
            "Russian Hill": 13
        },
        "Chinatown": {
            "Bayview": 22,
            "Nob Hill": 8,
            "Union Square": 7,
            "The Castro": 22,
            "Presidio": 19,
            "Pacific Heights": 10,
            "Russian Hill": 7
        },
        "The Castro": {
            "Bayview": 19,
            "Nob Hill": 16,
            "Union Square": 19,
            "Chinatown": 20,
            "Presidio": 20,
            "Pacific Heights": 16,
            "Russian Hill": 18
        },
        "Presidio": {
            "Bayview": 31,
            "Nob Hill": 18,
            "Union Square": 22,
            "Chinatown": 21,
            "The Castro": 21,
            "Pacific Heights": 11,
            "Russian Hill": 14
        },
        "Pacific Heights": {
            "Bayview": 22,
            "Nob Hill": 8,
            "Union Square": 12,
            "Chinatown": 11,
            "The Castro": 16,
            "Presidio": 11,
            "Russian Hill": 7
        },
        "Russian Hill": {
            "Bayview": 23,
            "Nob Hill": 5,
            "Union Square": 11,
            "Chinatown": 9,
            "The Castro": 21,
            "Presidio": 14,
            "Pacific Heights": 7
        }
    }
    
    # Friends data: name, location, available start and end (in minutes from 9:00 AM), minimum duration
    friends = [
        {"name": "Paul", "location": "Nob Hill", "start_avail": 435, "end_avail": 735, "min_duration": 60},
        {"name": "Carol", "location": "Union Square", "start_avail": 540, "end_avail": 675, "min_duration": 120},
        {"name": "Patricia", "location": "Chinatown", "start_avail": 660, "end_avail": 750, "min_duration": 75},
        {"name": "Karen", "location": "The Castro", "start_avail": 480, "end_avail": 600, "min_duration": 45},
        {"name": "Nancy", "location": "Presidio", "start_avail": 165, "end_avail": 780, "min_duration": 30},
        {"name": "Jeffrey", "location": "Pacific Heights", "start_avail": 660, "end_avail": 705, "min_duration": 45},
        {"name": "Matthew", "location": "Russian Hill", "start_avail": 405, "end_avail": 765, "min_duration": 75}
    ]
    
    # Initialize Z3 solver and optimization
    opt = Optimize()
    
    # Create variables for each friend: whether we meet them, and their start and end times
    meet_vars = []
    start_vars = []
    end_vars = []
    for i, friend in enumerate(friends):
        meet_vars.append(Bool(f"meet_{friend['name']}"))
        start_vars.append(Int(f"start_{friend['name']}"))
        end_vars.append(Int(f"end_{friend['name']}"))
    
    # Virtual start at Bayview at time 0
    virtual_start = 0
    virtual_location = "Bayview"
    
    # Constraints for each friend
    for i, friend in enumerate(friends):
        meet = meet_vars[i]
        start = start_vars[i]
        end = end_vars[i]
        # If we meet, then constraints on time window and duration
        opt.add(Implies(meet, start >= friend["start_avail"]))
        opt.add(Implies(meet, end <= friend["end_avail"]))
        opt.add(Implies(meet, end - start >= friend["min_duration"]))
        # Travel from Bayview to this meeting if it's the first one
        opt.add(Implies(meet, start >= travel_times[virtual_location][friend["location"]]))
    
    # Constraints for travel between meetings
    for i in range(len(friends)):
        for j in range(i+1, len(friends)):
            meet_i = meet_vars[i]
            meet_j = meet_vars[j]
            start_i = start_vars[i]
            end_i = end_vars[i]
            start_j = start_vars[j]
            end_j = end_vars[j]
            loc_i = friends[i]["location"]
            loc_j = friends[j]["location"]
            # If both meetings happen, then one must occur after the other with travel time
            opt.add(Implies(And(meet_i, meet_j),
                         Or(end_i + travel_times[loc_i][loc_j] <= start_j,
                            end_j + travel_times[loc_j][loc_i] <= start_i)))
    
    # Maximize the number of meetings
    opt.maximize(Sum([If(meet, 1, 0) for meet in meet_vars]))
    
    # Check if a solution exists
    if opt.check() == sat:
        model = opt.model()
        itinerary = []
        for i, friend in enumerate(friends):
            if is_true(model.eval(meet_vars[i])):
                start_val = model.eval(start_vars[i]).as_long()
                end_val = model.eval(end_vars[i]).as_long()
                # Convert minutes to time string
                start_hour = 9 + start_val // 60
                start_minute = start_val % 60
                end_hour = 9 + end_val // 60
                end_minute = end_val % 60
                start_str = f"{start_hour}:{start_minute:02d}"
                end_str = f"{end_hour}:{end_minute:02d}"
                itinerary.append({
                    "action": "meet",
                    "location": friend["location"],
                    "person": friend["name"],
                    "start_time": start_str,
                    "end_time": end_str
                })
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: x["start_time"])
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()