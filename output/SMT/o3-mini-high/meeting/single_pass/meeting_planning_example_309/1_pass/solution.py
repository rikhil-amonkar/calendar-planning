from z3 import *
import json

def minutes_to_time(mins):
    # Convert minutes from midnight to HH:MM in 24-hour format.
    h = mins // 60
    m = mins % 60
    return f"{h:02d}:{m:02d}"

def main():
    # Data for each friend: availability (in minutes from midnight), minimum meeting duration (in minutes), and location.
    # Times: 9:30 = 570, 13:30 = 810, 7:00 = 420, 21:00 = 1260, 11:15 = 675, 13:45 = 825, 8:30 = 510.
    friends = {
        "Nancy": {
            "avail_start": 570,  # 09:30
            "avail_end": 810,    # 13:30
            "duration": 90,
            "location": "Chinatown"
        },
        "Mary": {
            "avail_start": 420,  # 07:00
            "avail_end": 1260,   # 21:00
            "duration": 75,
            "location": "Alamo Square"
        },
        "Jessica": {
            "avail_start": 675,  # 11:15
            "avail_end": 825,    # 13:45
            "duration": 45,
            "location": "Bayview"
        },
        "Rebecca": {
            "avail_start": 420,  # 07:00
            "avail_end": 510,    # 08:30
            "duration": 45,
            "location": "Fisherman's Wharf"
        }
    }
    
    # You start at the Financial District at 09:00 (540 minutes from midnight).
    start_location = "Financial District"
    start_time = 540  # 09:00
    
    # Travel times (in minutes) between locations.
    travel = {
        "Financial District": {
            "Chinatown": 5,
            "Alamo Square": 17,
            "Bayview": 19,
            "Fisherman's Wharf": 10
        },
        "Chinatown": {
            "Financial District": 5,
            "Alamo Square": 17,
            "Bayview": 22,
            "Fisherman's Wharf": 8
        },
        "Alamo Square": {
            "Financial District": 17,
            "Chinatown": 16,
            "Bayview": 16,
            "Fisherman's Wharf": 19
        },
        "Bayview": {
            "Financial District": 19,
            "Chinatown": 18,
            "Alamo Square": 16,
            "Fisherman's Wharf": 25
        },
        "Fisherman's Wharf": {
            "Financial District": 11,
            "Chinatown": 12,
            "Alamo Square": 20,
            "Bayview": 26
        }
    }
    
    opt = Optimize()
    
    # For each friend, create:
    #   scheduled - a Boolean (whether you decide to meet this friend)
    #   start - an integer for the meeting start time (minutes from midnight)
    #   end - an integer for the meeting end time
    #   order - an integer that indicates the order (1 for the first meeting, 2 for the second, etc.)
    scheduled = {}
    start_vars = {}
    end_vars = {}
    order_vars = {}
    
    num_friends = len(friends)
    for name, data in friends.items():
        scheduled[name] = Bool(f"scheduled_{name}")
        start_vars[name] = Int(f"start_{name}")
        end_vars[name] = Int(f"end_{name}")
        order_vars[name] = Int(f"order_{name}")
        
        # Basic domain constraints for times.
        opt.add(start_vars[name] >= 0)
        opt.add(end_vars[name] >= 0)
        # Order can range from 0 (meaning not scheduled) up to num_friends.
        opt.add(order_vars[name] >= 0, order_vars[name] <= num_friends)
        
        # If a meeting is scheduled, it must occur during the friend's available window with at least the required duration.
        opt.add(Implies(scheduled[name],
                        And(start_vars[name] >= data["avail_start"],
                            end_vars[name] <= data["avail_end"],
                            end_vars[name] - start_vars[name] >= data["duration"])))
        # If not scheduled, force the order to be 0.
        opt.add(Implies(Not(scheduled[name]), order_vars[name] == 0))
        # If scheduled, assign an order number 1 or higher.
        opt.add(Implies(scheduled[name], order_vars[name] >= 1))
    
    # For the very first meeting (order == 1), you must travel from the Financial District.
    for name, data in friends.items():
        opt.add(Implies(And(scheduled[name], order_vars[name] == 1),
                        start_vars[name] >= start_time + travel[start_location][data["location"]]))
    
    friend_names = list(friends.keys())
    # For any two meetings that are both scheduled, enforce an ordering and travel time between them.
    for i in range(len(friend_names)):
        for j in range(i+1, len(friend_names)):
            name_i = friend_names[i]
            name_j = friend_names[j]
            loc_i = friends[name_i]["location"]
            loc_j = friends[name_j]["location"]
            # If both are scheduled, they must have different order numbers.
            opt.add(Implies(And(scheduled[name_i], scheduled[name_j]), order_vars[name_i] != order_vars[name_j]))
            
            # If meeting i comes before meeting j, then meeting j must start after meeting i ends plus travel time.
            opt.add(Implies(And(scheduled[name_i], scheduled[name_j], order_vars[name_i] < order_vars[name_j]),
                        start_vars[name_j] >= end_vars[name_i] + travel[loc_i][loc_j]))
            # Conversely, if meeting j comes before meeting i.
            opt.add(Implies(And(scheduled[name_i], scheduled[name_j], order_vars[name_j] < order_vars[name_i]),
                        start_vars[name_i] >= end_vars[name_j] + travel[loc_j][loc_i]))
    
    # Objective: maximize the number of meetings scheduled.
    total_meetings = Sum([If(scheduled[name], 1, 0) for name in friend_names])
    opt.maximize(total_meetings)
    
    # Try to solve the scheduling problem.
    if opt.check() == sat:
        model = opt.model()
        # Gather scheduled meetings along with their order.
        meetings = []
        for name in friend_names:
            if is_true(model.evaluate(scheduled[name])):
                order_val = model.evaluate(order_vars[name]).as_long()
                start_val = model.evaluate(start_vars[name]).as_long()
                end_val = model.evaluate(end_vars[name]).as_long()
                meetings.append((order_val, name, start_val, end_val))
        # Sort the meetings by their order.
        meetings.sort(key=lambda x: x[0])
        
        itinerary = []
        for order_val, name, s, e in meetings:
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": minutes_to_time(s),
                "end_time": minutes_to_time(e)
            })
        # Output the itinerary as a JSON-formatted dictionary.
        output = {"itinerary": itinerary}
        print(json.dumps(output, indent=2))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()