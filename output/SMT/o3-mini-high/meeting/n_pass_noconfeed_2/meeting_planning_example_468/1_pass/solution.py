from z3 import *
import json

# Convert minutes since midnight to a string in H:MM 24-hour format.
def minutes_to_time_str(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

def main():
    # Friend meeting data.
    # Each friend is met at a specific location with an available interval (in minutes) and a minimum meeting duration of 90 minutes.
    # Times are in minutes since midnight.
    # 9:00 AM => 540, 12:45 PM => 765, 9:45 PM => 1305, etc.
    friends = [
        {"name": "Rebecca", "location": "Bayview", "avail_start": 540, "avail_end": 765},
        {"name": "Amanda", "location": "Pacific Heights", "avail_start": 1110, "avail_end": 1305},
        {"name": "James", "location": "Alamo Square", "avail_start": 585, "avail_end": 1275},
        {"name": "Sarah", "location": "Fisherman's Wharf", "avail_start": 480, "avail_end": 1290},
        {"name": "Melissa", "location": "Golden Gate Park", "avail_start": 540, "avail_end": 1125}
    ]
    n_friends = len(friends)
    meeting_duration = 90

    # Travel times (in minutes) given from one location to another.
    # The matrix M[i][j] gives the travel time from friends[i]'s location to friends[j]'s location.
    # Friend indices correspond to:
    # 0: Rebecca at Bayview
    # 1: Amanda at Pacific Heights
    # 2: James at Alamo Square
    # 3: Sarah at Fisherman's Wharf
    # 4: Melissa at Golden Gate Park
    M = [
        [0, 23, 16, 25, 22],   # From Bayview
        [22, 0, 10, 13, 15],    # From Pacific Heights
        [16, 10, 0, 19, 9],      # From Alamo Square
        [26, 12, 20, 0, 25],     # From Fisherman's Wharf
        [23, 16, 10, 24, 0]      # From Golden Gate Park
    ]
    # Travel times from starting location "The Castro" (arrival at 9:00 AM i.e. 540) to each friend location.
    castro_travel = [
        19,  # The Castro -> Bayview (Rebecca)
        16,  # The Castro -> Pacific Heights (Amanda)
        8,   # The Castro -> Alamo Square (James)
        24,  # The Castro -> Fisherman's Wharf (Sarah)
        11   # The Castro -> Golden Gate Park (Melissa)
    ]
    
    # We use a slot-based formulation.
    # We have 5 available slots (the maximum possible meetings).
    # Each slot will either hold a friend's meeting (indicated by an integer in 0..4)
    # or be empty (indicated by -1). The slots must appear in contiguous order.
    max_slots = n_friends
    opt = Optimize()

    slot_vars = [Int(f"slot_{i}") for i in range(max_slots)]
    t_vars = [Int(f"t_{i}") for i in range(max_slots)]  # Start time (in minutes) for the meeting in slot i

    # For each slot, add domain constraints.
    for i in range(max_slots):
        # slot value is either -1 (empty) or one of 0, 1, 2, 3, 4.
        opt.add(Or(slot_vars[i] == -1, And(slot_vars[i] >= 0, slot_vars[i] < n_friends)))
        # Meeting start time must be within the day (0 to 1440 minutes).
        opt.add(t_vars[i] >= 0, t_vars[i] <= 1440)
        
        # If this slot is filled, then the meeting must occur within the friend's available window.
        # We use nested If's to choose the correct constraints.
        avail_constraint = If(slot_vars[i] == 0,
                              And(t_vars[i] >= friends[0]["avail_start"], t_vars[i] + meeting_duration <= friends[0]["avail_end"]),
                         If(slot_vars[i] == 1,
                              And(t_vars[i] >= friends[1]["avail_start"], t_vars[i] + meeting_duration <= friends[1]["avail_end"]),
                         If(slot_vars[i] == 2,
                              And(t_vars[i] >= friends[2]["avail_start"], t_vars[i] + meeting_duration <= friends[2]["avail_end"]),
                         If(slot_vars[i] == 3,
                              And(t_vars[i] >= friends[3]["avail_start"], t_vars[i] + meeting_duration <= friends[3]["avail_end"]),
                         If(slot_vars[i] == 4,
                              And(t_vars[i] >= friends[4]["avail_start"], t_vars[i] + meeting_duration <= friends[4]["avail_end"]),
                              True)))))
        opt.add(Implies(slot_vars[i] != -1, avail_constraint))
        
        # For the first slot, add constraint to account for travel from The Castro.
        if i == 0:
            castro_constraint = If(slot_vars[0] == 0,
                                   t_vars[0] >= 540 + castro_travel[0],
                              If(slot_vars[0] == 1,
                                   t_vars[0] >= 540 + castro_travel[1],
                              If(slot_vars[0] == 2,
                                   t_vars[0] >= 540 + castro_travel[2],
                              If(slot_vars[0] == 3,
                                   t_vars[0] >= 540 + castro_travel[3],
                              If(slot_vars[0] == 4,
                                   t_vars[0] >= 540 + castro_travel[4],
                                   True)))))
            opt.add(Implies(slot_vars[0] != -1, castro_constraint))
        
        # Enforce contiguity: if a slot is empty, every later slot must be empty.
        if i > 0:
            opt.add(Implies(slot_vars[i-1] == -1, slot_vars[i] == -1))
    
    # Ensure that if two slots are filled then the same friend is not scheduled twice.
    for i in range(max_slots):
        for j in range(i + 1, max_slots):
            opt.add(Implies(And(slot_vars[i] != -1, slot_vars[j] != -1),
                            slot_vars[i] != slot_vars[j]))
    
    # For consecutive filled slots, add travel constraints.
    # If slot i-1 holds friend k and slot i holds friend l,
    # then the meeting in slot i must start at least (meeting_duration + travel_time from friend k to friend l) minutes after the meeting in slot i-1.
    for i in range(1, max_slots):
        for k in range(n_friends):
            for l in range(n_friends):
                opt.add(Implies(And(slot_vars[i-1] == k, slot_vars[i] == l),
                                t_vars[i-1] + meeting_duration + M[k][l] <= t_vars[i]))
    
    # The objective is to maximize the number of meetings scheduled.
    num_meetings = Sum([If(slot_vars[i] != -1, 1, 0) for i in range(max_slots)])
    h = opt.maximize(num_meetings)
    
    # Solve the optimization problem.
    if opt.check() == sat:
        model = opt.model()
        itinerary = []
        # Process slots in order.
        for i in range(max_slots):
            slot_val = model.evaluate(slot_vars[i]).as_long()
            if slot_val == -1:
                break  # No more meetings in later slots.
            start_time = model.evaluate(t_vars[i]).as_long()
            end_time = start_time + meeting_duration
            meeting = {
                "action": "meet",
                "location": friends[slot_val]["location"],
                "person": friends[slot_val]["name"],
                "start_time": minutes_to_time_str(start_time),
                "end_time": minutes_to_time_str(end_time)
            }
            itinerary.append(meeting)
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()