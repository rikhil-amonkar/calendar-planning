from z3 import *
import json

# Helper function to convert minutes-since-midnight to H:MM 24-hour format.
def minutes_to_str(m):
    hour = m // 60
    minute = m % 60
    return f"{hour}:{minute:02d}"

# Data for friends: name, location, availability [start, end] (in minutes), meeting duration (fixed 90 minutes)
# Times: 9:00 -> 540, 12:45 -> 765, 6:30PM -> 18:30 -> 1110, 9:45PM -> 21:45 -> 1305,
# 9:45AM -> 585, 9:15PM -> 21:15 -> 1275, 8:00AM -> 480, 9:30PM -> 21:30 -> 1290, 6:45PM -> 18:45 -> 1125.
friend_names = ["Rebecca", "Amanda", "James", "Sarah", "Melissa"]
friend_locations = ["Bayview", "Pacific Heights", "Alamo Square", "Fisherman's Wharf", "Golden Gate Park"]
friend_avail_start = [540, 1110, 585, 480, 540]  # earliest meeting start allowed
friend_avail_end   = [765, 1305, 1275, 1290, 1125]  # meeting must finish by these times
# Meeting duration is fixed at 90 minutes.
meeting_duration = 90

# For each friend, the feasible start time must be in [avail_start, avail_end - meeting_duration]
friend_start_lower = friend_avail_start
friend_start_upper = [friend_avail_end[i] - meeting_duration for i in range(len(friend_avail_end))]

# Travel times from "The Castro" to each friend's location:
# (Castro to Bayview = 19, Pacific Heights = 16, Alamo Square = 8, Fisherman's Wharf = 24, Golden Gate Park = 11)
travel_from_castro = [19, 16, 8, 24, 11]  # Indexed same as friends

# Travel times between friend locations. Using friend id indices corresponding to:
# 0: Bayview, 1: Pacific Heights, 2: Alamo Square, 3: Fisherman's Wharf, 4: Golden Gate Park.
travel_table = {
    (0, 1): 23, (0, 2): 16, (0, 3): 25, (0, 4): 22,
    (1, 0): 22, (1, 2): 10, (1, 3): 13, (1, 4): 15,
    (2, 0): 16, (2, 1): 10, (2, 3): 19, (2, 4): 9,
    (3, 0): 26, (3, 1): 12, (3, 2): 20, (3, 4): 25,
    (4, 0): 23, (4, 1): 16, (4, 2): 10, (4, 3): 24
}
# Build list of possible pairs (a, b, travel_time) for consecutive meetings.
possible_pairs = []
for (a, b), t in travel_table.items():
    possible_pairs.append((a, b, t))

# We fix the number of meeting "slots" (the maximum possible number of meetings is 5).
S = 5

opt = Optimize()

# Arrays to hold the slot assignment variables.
# For each slot, we assign an integer variable "slot_friend" with domain -1 ... 4.
# A value of -1 indicates that the slot is empty (i.e. no meeting scheduled).
slot_friend = [Int(f"slot_friend_{i}") for i in range(S)]
# For each slot, a meeting start time variable (in minutes since midnight).
slot_start = [Int(f"slot_start_{i}") for i in range(S)]

# Arrival time at The Castro is 9:00 (540 minutes)
arrival_time = 540

# Add domain constraints and availability constraints for each slot.
for i in range(S):
    # slot_friend[i] must be either -1 (empty) or a valid friend index 0..4.
    opt.add(Or(slot_friend[i] == -1, And(slot_friend[i] >= 0, slot_friend[i] < len(friend_names))))
    # If the slot is empty then fix its start time to 0.
    # Otherwise, the meeting start time must lie within the friend’s constraints.
    constraint = If(slot_friend[i] == -1,
                    slot_start[i] == 0,
                    Or(
                        And(slot_friend[i] == 0, slot_start[i] >= friend_start_lower[0], slot_start[i] <= friend_start_upper[0]),
                        And(slot_friend[i] == 1, slot_start[i] >= friend_start_lower[1], slot_start[i] <= friend_start_upper[1]),
                        And(slot_friend[i] == 2, slot_start[i] >= friend_start_lower[2], slot_start[i] <= friend_start_upper[2]),
                        And(slot_friend[i] == 3, slot_start[i] >= friend_start_lower[3], slot_start[i] <= friend_start_upper[3]),
                        And(slot_friend[i] == 4, slot_start[i] >= friend_start_lower[4], slot_start[i] <= friend_start_upper[4])
                    )
                   )
    opt.add(constraint)

# Enforce contiguity: If a later slot is filled, then all earlier slots must be filled.
for i in range(1, S):
    opt.add(Implies(slot_friend[i] != -1, slot_friend[i-1] != -1))

# Enforce that meetings in filled slots are distinct.
for i in range(S):
    for j in range(i+1, S):
        opt.add(Implies(And(slot_friend[i] != -1, slot_friend[j] != -1), slot_friend[i] != slot_friend[j]))

# Travel constraints:
# For the first meeting slot, ensure that we have enough time from The Castro to reach the meeting.
first_travel_constraint = Implies(slot_friend[0] != -1,
    Or(
        And(slot_friend[0] == 0, slot_start[0] >= arrival_time + travel_from_castro[0]),
        And(slot_friend[0] == 1, slot_start[0] >= arrival_time + travel_from_castro[1]),
        And(slot_friend[0] == 2, slot_start[0] >= arrival_time + travel_from_castro[2]),
        And(slot_friend[0] == 3, slot_start[0] >= arrival_time + travel_from_castro[3]),
        And(slot_friend[0] == 4, slot_start[0] >= arrival_time + travel_from_castro[4])
    )
)
opt.add(first_travel_constraint)

# For consecutive meeting slots, add travel time constraints.
for i in range(1, S):
    # Only enforce if both slots are filled.
    cons = Implies(And(slot_friend[i-1] != -1, slot_friend[i] != -1),
                   # For the particular assignment of friend indices, the start time must allow:
                   # previous meeting end time + travel time <= current meeting start time.
                   Or([And(slot_friend[i-1] == a, slot_friend[i] == b, 
                           slot_start[i] >= slot_start[i-1] + meeting_duration + t)
                       for (a, b, t) in possible_pairs]))
    opt.add(cons)

# Objective: maximize the number of meetings scheduled.
num_meetings = Sum([If(slot_friend[i] != -1, 1, 0) for i in range(S)])
h = opt.maximize(num_meetings)

# Solve the problem.
if opt.check() == sat:
    model = opt.model()
    itinerary = []
    for i in range(S):
        f_val = model.evaluate(slot_friend[i]).as_long()
        # If the slot is not scheduled, break since schedule is contiguous.
        if f_val == -1:
            break
        start_time_val = model.evaluate(slot_start[i]).as_long()
        end_time_val = start_time_val + meeting_duration
        itinerary.append({
            "action": "meet",
            "location": friend_locations[f_val],
            "person": friend_names[f_val],
            "start_time": minutes_to_str(start_time_val),
            "end_time": minutes_to_str(end_time_val)
        })
    output = {"itinerary": itinerary}
else:
    output = {"itinerary": []}

print(json.dumps(output, indent=2))