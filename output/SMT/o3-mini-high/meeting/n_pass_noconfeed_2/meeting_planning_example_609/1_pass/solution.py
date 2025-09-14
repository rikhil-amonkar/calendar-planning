from z3 import Optimize, Int, Bool, If, And, Or, Implies, Not, sat
import json

def main():
    # Define travel times (in minutes) as given
    travel = {
        ("Chinatown", "Mission District"): 18,
        ("Chinatown", "Alamo Square"): 17,
        ("Chinatown", "Pacific Heights"): 10,
        ("Chinatown", "Union Square"): 7,
        ("Chinatown", "Golden Gate Park"): 23,
        ("Chinatown", "Sunset District"): 29,
        ("Chinatown", "Presidio"): 19,
        
        ("Mission District", "Chinatown"): 16,
        ("Mission District", "Alamo Square"): 11,
        ("Mission District", "Pacific Heights"): 16,
        ("Mission District", "Union Square"): 15,
        ("Mission District", "Golden Gate Park"): 17,
        ("Mission District", "Sunset District"): 24,
        ("Mission District", "Presidio"): 25,
        
        ("Alamo Square", "Chinatown"): 16,
        ("Alamo Square", "Mission District"): 10,
        ("Alamo Square", "Pacific Heights"): 10,
        ("Alamo Square", "Union Square"): 14,
        ("Alamo Square", "Golden Gate Park"): 9,
        ("Alamo Square", "Sunset District"): 16,
        ("Alamo Square", "Presidio"): 18,
        
        ("Pacific Heights", "Chinatown"): 11,
        ("Pacific Heights", "Mission District"): 15,
        ("Pacific Heights", "Alamo Square"): 10,
        ("Pacific Heights", "Union Square"): 12,
        ("Pacific Heights", "Golden Gate Park"): 15,
        ("Pacific Heights", "Sunset District"): 21,
        ("Pacific Heights", "Presidio"): 11,
        
        ("Union Square", "Chinatown"): 7,
        ("Union Square", "Mission District"): 14,
        ("Union Square", "Alamo Square"): 15,
        ("Union Square", "Pacific Heights"): 15,
        ("Union Square", "Golden Gate Park"): 22,
        ("Union Square", "Sunset District"): 26,
        ("Union Square", "Presidio"): 24,
        
        ("Golden Gate Park", "Chinatown"): 23,
        ("Golden Gate Park", "Mission District"): 17,
        ("Golden Gate Park", "Alamo Square"): 10,
        ("Golden Gate Park", "Pacific Heights"): 16,
        ("Golden Gate Park", "Union Square"): 22,
        ("Golden Gate Park", "Sunset District"): 10,
        ("Golden Gate Park", "Presidio"): 11,
        
        ("Sunset District", "Chinatown"): 30,
        ("Sunset District", "Mission District"): 24,
        ("Sunset District", "Alamo Square"): 17,
        ("Sunset District", "Pacific Heights"): 21,
        ("Sunset District", "Union Square"): 30,
        ("Sunset District", "Golden Gate Park"): 11,
        ("Sunset District", "Presidio"): 16,
        
        ("Presidio", "Chinatown"): 21,
        ("Presidio", "Mission District"): 26,
        ("Presidio", "Alamo Square"): 18,
        ("Presidio", "Pacific Heights"): 11,
        ("Presidio", "Union Square"): 22,
        ("Presidio", "Golden Gate Park"): 12,
        ("Presidio", "Sunset District"): 15
    }

    # Friend meeting data: availability times in minutes since midnight
    # Times: 9:00 AM is 540.
    # David: 8:00 (480) to 19:45 (1185), min meeting 45
    # Kenneth: 14:00 (840) to 19:45 (1185), min meeting 120
    # John: 17:00 (1020) to 20:00 (1200), min meeting 15
    # Charles: 21:45 (1305) to 22:45 (1365), min meeting 60
    # Deborah: 7:00 (420) to 18:15 (1095), min meeting 90
    # Karen: 17:45 (1065) to 21:15 (1275), min meeting 15
    # Carol: 8:15 (495) to 9:15 (555), min meeting 30
    friends = [
        {"name": "David", "location": "Mission District", "avail_start": 480, "avail_end": 1185, "min_dur": 45},
        {"name": "Kenneth", "location": "Alamo Square", "avail_start": 840, "avail_end": 1185, "min_dur": 120},
        {"name": "John", "location": "Pacific Heights", "avail_start": 1020, "avail_end": 1200, "min_dur": 15},
        {"name": "Charles", "location": "Union Square", "avail_start": 1305, "avail_end": 1365, "min_dur": 60},
        {"name": "Deborah", "location": "Golden Gate Park", "avail_start": 420, "avail_end": 1095, "min_dur": 90},
        {"name": "Karen", "location": "Sunset District", "avail_start": 1065, "avail_end": 1275, "min_dur": 15},
        {"name": "Carol", "location": "Presidio", "avail_start": 495, "avail_end": 555, "min_dur": 30}
    ]
    num_friends = len(friends)
    
    # Starting parameters
    start_location = "Chinatown"
    start_time = 540  # 9:00 AM

    opt = Optimize()

    # Create decision variables for each friend meeting.
    meets = []       # Boolean: whether to meet the friend
    s_vars = []      # Start time of the meeting (in minutes)
    order_vars = []  # Order of the meeting in the itinerary (0 if not scheduled)
    
    for i in range(num_friends):
        meet_i = Bool(f"meet_{i}")
        s_i = Int(f"s_{i}")
        order_i = Int(f"order_{i}")
        meets.append(meet_i)
        s_vars.append(s_i)
        order_vars.append(order_i)
        
        # Domain for meeting start time, say within the day.
        opt.add(s_i >= 0, s_i <= 1440)
        
        # If not meeting, force s_i and order_i to 0.
        opt.add(Implies(Not(meet_i), s_i == 0))
        opt.add(Implies(Not(meet_i), order_i == 0))
        
        # If meeting is scheduled, order must be between 1 and num_friends.
        opt.add(Implies(meet_i, And(order_i >= 1, order_i <= num_friends)))
        
        # Meeting must be within friend availability and last long enough.
        friend = friends[i]
        opt.add(Implies(meet_i,
                        And(
                            s_i >= friend["avail_start"],
                            s_i + friend["min_dur"] <= friend["avail_end"]
                        )))
    
    # Ensure that if two meetings are scheduled, they have unique order numbers.
    for i in range(num_friends):
        for j in range(i+1, num_friends):
            opt.add(Implies(And(meets[i], meets[j]), order_vars[i] != order_vars[j]))
    
    # Chain constraints:
    # For the first scheduled meeting (order == 1), ensure we can get there from the start location.
    for i in range(num_friends):
        friend = friends[i]
        # Travel time from start_location to the friend's meeting location.
        ttime = travel[(start_location, friend["location"])]
        opt.add(Implies(And(meets[i], order_vars[i] == 1), s_vars[i] >= start_time + ttime))
    
    # For every meeting with order k > 1, ensure there is a predecessor meeting with order (k - 1)
    # such that the travel from the predecessor's location plus its meeting duration fits.
    for i in range(num_friends):
        friend_i = friends[i]
        for k in range(2, num_friends + 1):
            # For meeting i with order k, there must be some meeting j (j != i) with order (k-1)
            # such that s_i is at least s_j + min_dur_j + travel_time from friend j's location to friend i's location.
            pred_options = []
            for j in range(num_friends):
                if j == i:
                    continue
                friend_j = friends[j]
                ttime = travel[(friend_j["location"], friend_i["location"])]
                pred_options.append(And(meets[j], order_vars[j] == k - 1, s_vars[i] >= s_vars[j] + friend_j["min_dur"] + ttime))
            if pred_options:
                opt.add(Implies(And(meets[i], order_vars[i] == k), Or(pred_options)))
    
    # Objective: maximize the number of meetings scheduled.
    total_meetings = sum([If(meet, 1, 0) for meet in meets])
    opt.maximize(total_meetings)
    
    if opt.check() == sat:
        model = opt.model()
        # Collect scheduled meetings with their order and start time.
        scheduled = []
        for i in range(num_friends):
            if model.evaluate(meets[i]):
                order_val = model.evaluate(order_vars[i]).as_long()
                s_val = model.evaluate(s_vars[i]).as_long()
                scheduled.append((order_val, i, s_val))
        # Sort by the order in the itinerary.
        scheduled.sort(key=lambda x: x[0])
        
        itinerary = []
        for order_val, i, s_val in scheduled:
            friend = friends[i]
            start_meet = s_val
            end_meet = s_val + friend["min_dur"]
            # Format times in H:MM (24-hour), no leading zero for hours.
            start_str = f"{start_meet // 60}:{start_meet % 60:02d}"
            end_str = f"{end_meet // 60}:{end_meet % 60:02d}"
            itinerary.append({
                "action": "meet",
                "location": friend["location"],
                "person": friend["name"],
                "start_time": start_str,
                "end_time": end_str
            })
        
        output = {"itinerary": itinerary}
        print(json.dumps(output, indent=2))
    else:
        print(json.dumps({"itinerary": []}, indent=2))

if __name__ == "__main__":
    main()