from z3 import Optimize, Int, Bool, If, And, Or, Implies, Not, sat
import json

def minutes_to_time_str(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

def main():
    # Friend availability and location data
    friends = ["Nancy", "Mary", "Jessica", "Rebecca"]
    friend_data = {
        "Nancy": {"location": "Chinatown", "avail_start": 570, "avail_end": 810, "min_meeting": 90},         # 9:30-13:30, 90 minutes
        "Mary": {"location": "Alamo Square", "avail_start": 420, "avail_end": 1260, "min_meeting": 75},      # 7:00-21:00, 75 minutes
        "Jessica": {"location": "Bayview", "avail_start": 675, "avail_end": 825, "min_meeting": 45},           # 11:15-13:45, 45 minutes
        "Rebecca": {"location": "Fisherman's Wharf", "avail_start": 420, "avail_end": 510, "min_meeting": 45}  # 7:00-8:30, 45 minutes
    }
    
    # Travel times (in minutes)
    travel_times = {
        ("Financial District", "Chinatown"): 5,
        ("Financial District", "Alamo Square"): 17,
        ("Financial District", "Bayview"): 19,
        ("Financial District", "Fisherman's Wharf"): 10,
        ("Chinatown", "Financial District"): 5,
        ("Chinatown", "Alamo Square"): 17,
        ("Chinatown", "Bayview"): 22,
        ("Chinatown", "Fisherman's Wharf"): 8,
        ("Alamo Square", "Financial District"): 17,
        ("Alamo Square", "Chinatown"): 16,
        ("Alamo Square", "Bayview"): 16,
        ("Alamo Square", "Fisherman's Wharf"): 19,
        ("Bayview", "Financial District"): 19,
        ("Bayview", "Chinatown"): 18,
        ("Bayview", "Alamo Square"): 16,
        ("Bayview", "Fisherman's Wharf"): 25,
        ("Fisherman's Wharf", "Financial District"): 11,
        ("Fisherman's Wharf", "Chinatown"): 12,
        ("Fisherman's Wharf", "Alamo Square"): 20,
        ("Fisherman's Wharf", "Bayview"): 26
    }
    
    # You start at Financial District at 9:00 AM (540 minutes)
    fd_location = "Financial District"
    start_fd = 540

    # Create the optimizer and decision variables
    opt = Optimize()

    # For each friend, create variables for whether to meet, meeting start and end times, and ordering
    meeting_vars = {}
    for f in friends:
        meet = Bool(f"meet_{f}")
        start_time = Int(f"start_{f}")
        end_time = Int(f"end_{f}")
        order = Int(f"order_{f}")
        meeting_vars[f] = {"meet": meet, "start": start_time, "end": end_time, "order": order}
        
        # If not meeting, we force start and end to 0 for consistency.
        opt.add(Or(meet, start_time == 0))
        opt.add(Or(meet, end_time == 0))
        
        # If meeting is scheduled, enforce available time window and minimum meeting duration.
        opt.add(Implies(meet, start_time >= friend_data[f]["avail_start"]))
        opt.add(Implies(meet, end_time <= friend_data[f]["avail_end"]))
        opt.add(Implies(meet, end_time - start_time >= friend_data[f]["min_meeting"]))
        # If meeting, restrict order to a plausible range.
        opt.add(Implies(meet, And(order >= 0, order <= len(friends) - 1)))
    
    # For any two meetings that are both scheduled, ensure they are ordered and separated by travel time.
    for i in range(len(friends)):
        for j in range(i + 1, len(friends)):
            f_i = friends[i]
            f_j = friends[j]
            vars_i = meeting_vars[f_i]
            vars_j = meeting_vars[f_j]
            
            # If both meetings are scheduled, orders must be different.
            opt.add(Implies(And(vars_i["meet"], vars_j["meet"]), vars_i["order"] != vars_j["order"]))
            
            # Compute required travel times between the two friend locations.
            travel_i_j = travel_times[(friend_data[f_i]["location"], friend_data[f_j]["location"])]
            travel_j_i = travel_times[(friend_data[f_j]["location"], friend_data[f_i]["location"])]
            
            # Enforce disjunctive ordering with travel time separation.
            opt.add(Implies(
                And(vars_i["meet"], vars_j["meet"]),
                Or(
                    And(vars_i["order"] < vars_j["order"],
                        vars_j["start"] >= vars_i["end"] + travel_i_j),
                    And(vars_j["order"] < vars_i["order"],
                        vars_i["start"] >= vars_j["end"] + travel_j_i)
                )
            ))
    
    # For the first meeting in the itinerary, ensure that you can travel from the Financial District.
    for f in friends:
        # f is the first meeting if for every other friend g that is scheduled, order_f <= order_g.
        first_condition = And([Or(Not(meeting_vars[g]["meet"]), meeting_vars[f]["order"] <= meeting_vars[g]["order"]) 
                               for g in friends if g != f])
        travel_from_fd = travel_times[(fd_location, friend_data[f]["location"])]
        opt.add(Implies(
            And(meeting_vars[f]["meet"], first_condition),
            meeting_vars[f]["start"] >= start_fd + travel_from_fd
        ))
    
    # Objective: maximize the number of meetings scheduled.
    total_meetings = sum([If(meeting_vars[f]["meet"], 1, 0) for f in friends])
    opt.maximize(total_meetings)
    
    # Check for a solution and extract the itinerary.
    if opt.check() == sat:
        model = opt.model()
        scheduled_meetings = []
        for f in friends:
            if model.evaluate(meeting_vars[f]["meet"]):
                order_val = model.evaluate(meeting_vars[f]["order"]).as_long()
                start_val = model.evaluate(meeting_vars[f]["start"]).as_long()
                end_val = model.evaluate(meeting_vars[f]["end"]).as_long()
                scheduled_meetings.append((order_val, f, friend_data[f]["location"], start_val, end_val))
        # Sort the scheduled meetings by their order.
        scheduled_meetings.sort(key=lambda x: x[0])
        itinerary = []
        for _, person, location, start_val, end_val in scheduled_meetings:
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": person,
                "start_time": minutes_to_time_str(start_val),
                "end_time": minutes_to_time_str(end_val)
            })
        output = {"itinerary": itinerary}
        print(json.dumps(output))
    else:
        # No feasible itinerary found.
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()