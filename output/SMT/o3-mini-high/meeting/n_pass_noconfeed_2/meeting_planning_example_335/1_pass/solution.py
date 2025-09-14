import json
from z3 import *

def main():
    # Define meeting data for each friend.
    # Times are in minutes from midnight.
    friends = {
        "Helen": {
            "location": "North Beach",
            "avail_start": 540,   # 9:00
            "avail_end": 1020,    # 17:00
            "duration": 15
        },
        "Betty": {
            "location": "Financial District",
            "avail_start": 1140,  # 19:00
            "avail_end": 1305,    # 21:45
            "duration": 90
        },
        "Amanda": {
            "location": "Alamo Square",
            "avail_start": 1185,  # 19:45
            "avail_end": 1260,    # 21:00
            "duration": 60
        },
        "Kevin": {
            "location": "Mission District",
            "avail_start": 645,   # 10:45
            "avail_end": 885,     # 14:45
            "duration": 45
        }
    }
    # Define travel times (in minutes) between locations.
    travel = {
        "Pacific Heights": {
            "North Beach": 9,
            "Financial District": 13,
            "Alamo Square": 10,
            "Mission District": 15
        },
        "North Beach": {
            "Pacific Heights": 8,
            "Financial District": 8,
            "Alamo Square": 16,
            "Mission District": 18
        },
        "Financial District": {
            "Pacific Heights": 13,
            "North Beach": 7,
            "Alamo Square": 17,
            "Mission District": 17
        },
        "Alamo Square": {
            "Pacific Heights": 10,
            "North Beach": 15,
            "Financial District": 17,
            "Mission District": 10
        },
        "Mission District": {
            "Pacific Heights": 16,
            "North Beach": 17,
            "Financial District": 17,
            "Alamo Square": 11
        }
    }
    
    start_location = "Pacific Heights"
    arrival_time = 540  # 9:00 AM in minutes

    # Create an Optimize object.
    opt = Optimize()

    # Decision variables for each friend:
    # scheduled: whether you meet the friend.
    # start_time: start time of the meeting (if scheduled).
    # order: the order index in the itinerary (0 if not scheduled).
    scheduled = {}
    start_time_vars = {}
    order_vars = {}
    
    for name in friends:
        scheduled[name] = Bool(f"scheduled_{name}")
        start_time_vars[name] = Int(f"start_{name}")
        order_vars[name] = Int(f"order_{name}")
    
    # Add constraints for each friend if they are scheduled.
    for name, info in friends.items():
        avail_start = info["avail_start"]
        avail_end = info["avail_end"]
        duration = info["duration"]
        # If scheduled, meeting must start no earlier than avail_start
        opt.add(Implies(scheduled[name], start_time_vars[name] >= avail_start))
        # Meeting must finish (start + duration) by avail_end.
        opt.add(Implies(scheduled[name], start_time_vars[name] + duration <= avail_end))
        # If scheduled, assign an order number between 1 and number of friends.
        opt.add(Implies(scheduled[name], And(order_vars[name] >= 1, order_vars[name] <= len(friends))))
        # If not scheduled, order is set to 0.
        opt.add(Implies(Not(scheduled[name]), order_vars[name] == 0))
    
    friend_names = list(friends.keys())
    # Ensure that if two meetings are scheduled, they have different order numbers.
    for i in range(len(friend_names)):
        for j in range(i+1, len(friend_names)):
            n1 = friend_names[i]
            n2 = friend_names[j]
            opt.add(Implies(And(scheduled[n1], scheduled[n2]), order_vars[n1] != order_vars[n2]))
    
    # For the first meeting in the itinerary, account for travel from the starting location.
    for name, info in friends.items():
        loc = info["location"]
        travel_time_from_start = travel[start_location][loc]
        opt.add(Implies(And(scheduled[name], order_vars[name] == 1),
                        start_time_vars[name] >= arrival_time + travel_time_from_start))
    
    # Enforce travel constraints for consecutive meetings.
    # For any two different friends i and j:
    # if meeting j directly follows meeting i then meeting j must start after meeting i ends plus travel time.
    for i in friend_names:
        for j in friend_names:
            if i != j:
                travel_time_ij = travel[friends[i]["location"]][friends[j]["location"]]
                opt.add(Implies(And(scheduled[i], scheduled[j], order_vars[j] == order_vars[i] + 1),
                                start_time_vars[j] >= start_time_vars[i] + friends[i]["duration"] + travel_time_ij))
    
    # Optionally, enforce that meetings occur in increasing order of start time.
    for i in friend_names:
        for j in friend_names:
            if i != j:
                opt.add(Implies(And(scheduled[i], scheduled[j], order_vars[i] < order_vars[j]),
                                start_time_vars[i] < start_time_vars[j]))
    
    # Objective: maximize the number of meetings scheduled.
    meeting_count = Sum([If(scheduled[name], 1, 0) for name in friend_names])
    h1 = opt.maximize(meeting_count)
    # Secondary objective: minimize the total start time for scheduled meetings (to favor earlier schedules).
    total_start = Sum([If(scheduled[name], start_time_vars[name], 0) for name in friend_names])
    h2 = opt.minimize(total_start)
    
    # Check for a solution.
    if opt.check() == sat:
        model = opt.model()
        itinerary = []
        scheduled_meetings = []
        # Collect scheduled meetings with their order, start and end times.
        for name in friend_names:
            if is_true(model.evaluate(scheduled[name])):
                ord_val = model.evaluate(order_vars[name]).as_long()
                st = model.evaluate(start_time_vars[name]).as_long()
                et = st + friends[name]["duration"]
                scheduled_meetings.append((ord_val, name, friends[name]["location"], st, et))
        # Sort meetings by their order.
        scheduled_meetings.sort(key=lambda x: x[0])
        
        # Function to convert minutes into "H:MM" 24-hour format.
        def format_time(minutes):
            hr = minutes // 60
            mn = minutes % 60
            return f"{hr}:{mn:02d}"
        
        for ord_val, name, loc, st, et in scheduled_meetings:
            itinerary.append({
                "action": "meet",
                "location": loc,
                "person": name,
                "start_time": format_time(st),
                "end_time": format_time(et)
            })
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()