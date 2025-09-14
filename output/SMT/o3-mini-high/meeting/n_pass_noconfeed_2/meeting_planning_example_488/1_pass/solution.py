from z3 import *
import json

def minutes_to_time(m):
    # Convert minutes (from midnight) to a string in "H:MM" format.
    h = m // 60
    mins = m % 60
    return f"{h}:{mins:02d}"

def main():
    # Travel times (in minutes) between locations.
    travel = {
        "Pacific Heights": {"Nob Hill": 8, "Russian Hill": 7, "The Castro": 16, "Sunset District": 21, "Haight-Ashbury": 11},
        "Nob Hill": {"Pacific Heights": 8, "Russian Hill": 5, "The Castro": 17, "Sunset District": 25, "Haight-Ashbury": 13},
        "Russian Hill": {"Pacific Heights": 7, "Nob Hill": 5, "The Castro": 21, "Sunset District": 23, "Haight-Ashbury": 17},
        "The Castro": {"Pacific Heights": 16, "Nob Hill": 17, "Russian Hill": 18, "Sunset District": 17, "Haight-Ashbury": 6},
        "Sunset District": {"Pacific Heights": 21, "Nob Hill": 27, "Russian Hill": 24, "The Castro": 17, "Haight-Ashbury": 15},
        "Haight-Ashbury": {"Pacific Heights": 12, "Nob Hill": 15, "Russian Hill": 17, "The Castro": 6, "Sunset District": 15},
    }
    
    # Meeting candidate information.
    # Times are represented as minutes from midnight.
    # 9:00 AM is 540, 10:00 AM is 600, etc.
    meetings = [
        {"name": "Ronald",   "location": "Nob Hill",       "avail_start": 600,  "avail_end": 1020, "min_duration": 105},  # 10:00-17:00
        {"name": "Sarah",    "location": "Russian Hill",   "avail_start": 435,  "avail_end": 570,  "min_duration": 45},   # 7:15-9:30
        {"name": "Helen",    "location": "The Castro",     "avail_start": 810,  "avail_end": 1020, "min_duration": 120},  # 13:30-17:00
        {"name": "Joshua",   "location": "Sunset District","avail_start": 855,  "avail_end": 1170, "min_duration": 90},   # 14:15-19:30
        {"name": "Margaret", "location": "Haight-Ashbury", "avail_start": 615,  "avail_end": 1320, "min_duration": 60},   # 10:15-22:00
    ]
    
    num_meetings = len(meetings)
    # Arrival at Pacific Heights at 9:00 AM (540 minutes)
    arrival_time = 540
    start_loc = "Pacific Heights"
    
    opt = Optimize()
    
    # Create decision variables for each meeting: scheduled flag, meeting start time, and order in the day.
    scheduled = [Bool(f"scheduled_{i}") for i in range(num_meetings)]
    start_vars = [Int(f"start_{i}") for i in range(num_meetings)]
    order_vars = [Int(f"order_{i}") for i in range(num_meetings)]
    
    # For each meeting, add constraints based on availability and required meeting duration.
    for i, meet in enumerate(meetings):
        # If the meeting is scheduled, then the meeting must start within the available window.
        opt.add(Implies(scheduled[i], start_vars[i] >= meet["avail_start"]))
        opt.add(Implies(scheduled[i], start_vars[i] + meet["min_duration"] <= meet["avail_end"]))
        
        # If the meeting is scheduled and it is the first meeting (order == 1), then you must travel from Pacific Heights.
        opt.add(Implies(And(scheduled[i], order_vars[i] == 1),
                        start_vars[i] >= arrival_time + travel[start_loc][meet["location"]]))
        
        # If not scheduled, fix order to 0.
        opt.add(Implies(Not(scheduled[i]), order_vars[i] == 0))
        # If scheduled, enforce order to be between 1 and num_meetings.
        opt.add(Implies(scheduled[i], And(order_vars[i] >= 1, order_vars[i] <= num_meetings)))
    
    # Ensure that for any two scheduled meetings, the order numbers are distinct.
    for i in range(num_meetings):
        for j in range(i+1, num_meetings):
            opt.add(Implies(And(scheduled[i], scheduled[j]), order_vars[i] != order_vars[j]))
    
    # Add travel constraints between meetings.
    # For any two meetings i and j: if both are scheduled and meeting i comes before j (order_i < order_j),
    # then the end time of meeting i plus travel time from its location to meeting j's location must be <= start time of j.
    for i in range(num_meetings):
        for j in range(num_meetings):
            if i == j:
                continue
            travel_time_ij = travel[meetings[i]["location"]][meetings[j]["location"]]
            opt.add(Implies(And(scheduled[i], scheduled[j], order_vars[i] < order_vars[j]),
                        start_vars[i] + meetings[i]["min_duration"] + travel_time_ij <= start_vars[j]))
    
    # Objective: maximize the total number of meetings scheduled.
    total_meetings = Sum([If(scheduled[i], 1, 0) for i in range(num_meetings)])
    opt.maximize(total_meetings)
    
    if opt.check() == sat:
        mod = opt.model()
        scheduled_list = []
        # Collect scheduled meetings with computed order and times.
        for i, meet in enumerate(meetings):
            if is_true(mod.evaluate(scheduled[i])):
                order_val = mod.evaluate(order_vars[i]).as_long()
                start_val = mod.evaluate(start_vars[i]).as_long()
                end_val = start_val + meet["min_duration"]
                scheduled_list.append((order_val, meet["name"], meet["location"], start_val, end_val))
        # Sort the scheduled meetings by their order.
        scheduled_list.sort(key=lambda x: x[0])
        itinerary = []
        for order_val, person, location, start_val, end_val in scheduled_list:
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": person,
                "start_time": minutes_to_time(start_val),
                "end_time": minutes_to_time(end_val)
            })
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        # If no schedule is found, return an empty itinerary.
        print(json.dumps({"itinerary": []}))

if __name__ == '__main__':
    main()