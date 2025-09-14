from z3 import *
import json

def minutes_to_time_str(m):
    # Convert minutes since midnight into "H:MM" format (24-hour; no leading zero for hour)
    hours = m // 60
    minutes = m % 60
    return f"{hours}:{minutes:02}"

def main():
    # Friend meeting information: available time window and minimum meeting duration (in minutes)
    # Times are represented in minutes from midnight.
    friend_info = [
        {"name": "Jessica", "location": "Golden Gate Park", "avail_start": 13*60+45, "avail_end": 15*60, "min_duration": 30},
        {"name": "Ashley",  "location": "Bayview",          "avail_start": 17*60+15, "avail_end": 20*60,   "min_duration": 105},
        {"name": "Ronald",  "location": "Chinatown",        "avail_start": 7*60+15,   "avail_end": 14*60+45,"min_duration": 90},
        {"name": "William", "location": "North Beach",      "avail_start": 13*60+15,  "avail_end": 20*60+15,"min_duration": 15},
        {"name": "Daniel",  "location": "Mission District", "avail_start": 7*60,      "avail_end": 11*60+15,"min_duration": 105}
    ]
    n = len(friend_info)

    # Travel time distances (in minutes) between locations.
    travel = {
        ("Presidio", "Golden Gate Park"): 12,
        ("Presidio", "Bayview"): 31,
        ("Presidio", "Chinatown"): 21,
        ("Presidio", "North Beach"): 18,
        ("Presidio", "Mission District"): 26,
        ("Golden Gate Park", "Presidio"): 11,
        ("Golden Gate Park", "Bayview"): 23,
        ("Golden Gate Park", "Chinatown"): 23,
        ("Golden Gate Park", "North Beach"): 24,
        ("Golden Gate Park", "Mission District"): 17,
        ("Bayview", "Presidio"): 31,
        ("Bayview", "Golden Gate Park"): 22,
        ("Bayview", "Chinatown"): 18,
        ("Bayview", "North Beach"): 21,
        ("Bayview", "Mission District"): 13,
        ("Chinatown", "Presidio"): 19,
        ("Chinatown", "Golden Gate Park"): 23,
        ("Chinatown", "Bayview"): 22,
        ("Chinatown", "North Beach"): 3,
        ("Chinatown", "Mission District"): 18,
        ("North Beach", "Presidio"): 17,
        ("North Beach", "Golden Gate Park"): 22,
        ("North Beach", "Bayview"): 22,
        ("North Beach", "Chinatown"): 6,
        ("North Beach", "Mission District"): 18,
        ("Mission District", "Presidio"): 25,
        ("Mission District", "Golden Gate Park"): 17,
        ("Mission District", "Bayview"): 15,
        ("Mission District", "Chinatown"): 16,
        ("Mission District", "North Beach"): 17,
    }

    # Starting conditions: you arrive at Presidio at 9:00 AM.
    start_location = "Presidio"
    arrival_time = 9 * 60  # 9:00 AM = 540 minutes

    # Create an Optimize object.
    opt = Optimize()

    # Decision variables:
    # For each friend i, scheduled[i] indicates if you meet that friend.
    # start_vars[i] and end_vars[i] are the meeting start and end times (in minutes).
    # order_vars[i] represents the position in the schedule if meeting is scheduled.
    scheduled = [Bool(f"scheduled_{i}") for i in range(n)]
    start_vars = [Int(f"start_{i}") for i in range(n)]
    end_vars = [Int(f"end_{i}") for i in range(n)]
    order_vars = [Int(f"order_{i}") for i in range(n)]

    # Time domain constraints: meeting times must be within the day.
    for i in range(n):
        opt.add(start_vars[i] >= 0, start_vars[i] <= 1440)
        opt.add(end_vars[i] >= 0, end_vars[i] <= 1440)

    # Meeting window and duration constraints.
    for i, friend in enumerate(friend_info):
        # If a meeting is scheduled, ensure it happens within the friend's availability and meets the minimum duration.
        opt.add(Implies(scheduled[i],
                        And(start_vars[i] >= friend["avail_start"],
                            end_vars[i] <= friend["avail_end"],
                            end_vars[i] - start_vars[i] >= friend["min_duration"])))
        # If not scheduled, force its order to be -1.
        opt.add(Implies(Not(scheduled[i]), order_vars[i] == -1))
        # If scheduled, order must be between 0 and n-1.
        opt.add(Implies(scheduled[i], And(order_vars[i] >= 0, order_vars[i] < n)))

    # Uniqueness of order: for any two scheduled meetings, they must have different order numbers.
    for i in range(n):
        for j in range(i+1, n):
            opt.add(Implies(And(scheduled[i], scheduled[j]),
                        order_vars[i] != order_vars[j]))

    # Travel constraints:
    # For the first meeting in the schedule, ensure you have traveled from Presidio.
    for i, friend in enumerate(friend_info):
        travel_time_val = travel[(start_location, friend["location"])]
        opt.add(Implies(And(scheduled[i], order_vars[i] == 0),
                        start_vars[i] >= arrival_time + travel_time_val))
    
    # For every pair of meetings, if meeting i is scheduled before meeting j then
    # meeting j must start only after traveling from friend i's location.
    for i in range(n):
        for j in range(n):
            if i != j:
                # Only enforce travel if both meetings are scheduled and i comes before j.
                travel_time_val = travel.get((friend_info[i]["location"], friend_info[j]["location"]))
                if travel_time_val is not None:
                    opt.add(Implies(And(scheduled[i], scheduled[j], order_vars[i] < order_vars[j]),
                                    start_vars[j] >= end_vars[i] + travel_time_val))
    
    # Optimization objective: maximize the number of friends met.
    opt.maximize(Sum([If(scheduled[i], 1, 0) for i in range(n)]))

    # Check for a solution.
    if opt.check() == sat:
        model = opt.model()
        # Extract scheduled meetings and sort them by their order.
        meetings = []
        for i in range(n):
            if is_true(model[scheduled[i]]):
                meetings.append((model[order_vars[i]].as_long(), i))
        meetings.sort(key=lambda x: x[0])
        itinerary = []
        for _, i in meetings:
            friend = friend_info[i]
            st = model[start_vars[i]].as_long()
            en = model[end_vars[i]].as_long()
            itinerary.append({
                "action": "meet",
                "location": friend["location"],
                "person": friend["name"],
                "start_time": minutes_to_time_str(st),
                "end_time": minutes_to_time_str(en)
            })
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()