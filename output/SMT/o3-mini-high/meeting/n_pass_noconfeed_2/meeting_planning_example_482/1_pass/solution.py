from z3 import *
import json

def format_time(t):
    hour = t // 60
    minute = t % 60
    return f"{hour}:{minute:02d}"

def main():
    opt = Optimize()

    # Define friend data
    friend_names = ["Stephanie", "Sandra", "Richard", "Brian", "Jason"]
    friend_locations = ["Mission District", "Bayview", "Pacific Heights", "Russian Hill", "Fisherman's Wharf"]
    avail_start = [8 * 60 + 15, 13 * 60, 7 * 60 + 15, 12 * 60 + 15, 8 * 60 + 30]  # in minutes: 495, 780, 435, 735, 510
    avail_end = [13 * 60 + 45, 19 * 60 + 30, 10 * 60 + 15, 16 * 60, 17 * 60 + 45]      # 825, 1170, 615, 960, 1065
    durations = [90, 15, 75, 120, 60]

    # Travel times from starting location ("Haight-Ashbury", arrival at 9:00 => 540 minutes)
    # Given: Haight-Ashbury to Mission District:11, Bayview:18, Pacific Heights:12, Russian Hill:17, Fisherman's Wharf:23.
    travel_from_start = [11, 18, 12, 17, 23]

    # Travel times between friend locations (rows: origin, cols: destination)
    # Order of locations: Mission District, Bayview, Pacific Heights, Russian Hill, Fisherman's Wharf.
    travel_between = [
        [0, 15, 16, 15, 22],   # From Mission District
        [13, 0, 23, 23, 25],   # From Bayview
        [15, 22, 0, 7, 13],    # From Pacific Heights
        [16, 23, 7, 0, 7],     # From Russian Hill
        [22, 26, 12, 7, 0]     # From Fisherman's Wharf
    ]

    num_slots = 5  # maximum number of friend meetings scheduled

    # Decision variables:
    # slots[i] is an integer indicating which friend is met in slot i, or -1 if the slot is unused.
    slots = [Int(f"slot_{i}") for i in range(num_slots)]
    # For each meeting slot, we define start and end times (in minutes after midnight).
    starts = [Int(f"start_{i}") for i in range(num_slots)]
    ends = [Int(f"end_{i}") for i in range(num_slots)]

    # Domain constraints for each slot and meeting times.
    for i in range(num_slots):
        # Slot is either -1 (unused) or one of 0,...,4 representing a friend.
        opt.add(slots[i] >= -1, slots[i] <= 4)
        # Bound meeting start and end times
        opt.add(starts[i] >= 0, starts[i] <= 1440)
        opt.add(ends[i] >= 0, ends[i] <= 1440)

    # If a slot is used (slot[i] != -1) then add constraints based on the friend assigned.
    for i in range(num_slots):
        opt.add(Implies(slots[i] >= 0,
                        And(
                            # When friend 0 (Stephanie) is assigned:
                            If(slots[i] == 0,
                               And(starts[i] >= avail_start[0],
                                   ends[i] <= avail_end[0],
                                   ends[i] - starts[i] >= durations[0]),
                               True),
                            # Friend 1 (Sandra)
                            If(slots[i] == 1,
                               And(starts[i] >= avail_start[1],
                                   ends[i] <= avail_end[1],
                                   ends[i] - starts[i] >= durations[1]),
                               True),
                            # Friend 2 (Richard)
                            If(slots[i] == 2,
                               And(starts[i] >= avail_start[2],
                                   ends[i] <= avail_end[2],
                                   ends[i] - starts[i] >= durations[2]),
                               True),
                            # Friend 3 (Brian)
                            If(slots[i] == 3,
                               And(starts[i] >= avail_start[3],
                                   ends[i] <= avail_end[3],
                                   ends[i] - starts[i] >= durations[3]),
                               True),
                            # Friend 4 (Jason)
                            If(slots[i] == 4,
                               And(starts[i] >= avail_start[4],
                                   ends[i] <= avail_end[4],
                                   ends[i] - starts[i] >= durations[4]),
                               True)
                        )))

    # Enforce contiguity: the meeting slots must be a contiguous prefix.
    for i in range(num_slots - 1):
        opt.add(Implies(slots[i] == -1, slots[i + 1] == -1))
        opt.add(Implies(slots[i + 1] != -1, slots[i] != -1))

    # Each friend can be scheduled at most once.
    for i in range(num_slots):
        for j in range(i + 1, num_slots):
            opt.add(Implies(And(slots[i] >= 0, slots[j] >= 0), slots[i] != slots[j]))

    # Travel time constraints:
    # For the first meeting slot, account for travel from the starting location "Haight-Ashbury" at 9:00 (540 minutes).
    for k in range(5):
        opt.add(Implies(slots[0] == k, 540 + travel_from_start[k] <= starts[0]))

    # For subsequent meeting slots, add travel constraints from the previous meeting location.
    for i in range(1, num_slots):
        for k in range(5):
            for j in range(5):
                opt.add(Implies(And(slots[i - 1] == k, slots[i] == j),
                                ends[i - 1] + travel_between[k][j] <= starts[i]))

    # Objective: maximize the number of meetings scheduled.
    meeting_count = Sum([If(slots[i] >= 0, 1, 0) for i in range(num_slots)])
    opt.maximize(meeting_count)

    if opt.check() == sat:
        model = opt.model()
        itinerary = []
        for i in range(num_slots):
            if model.evaluate(slots[i]).as_long() >= 0:
                friend_index = model.evaluate(slots[i]).as_long()
                start_time = model.evaluate(starts[i]).as_long()
                end_time = model.evaluate(ends[i]).as_long()
                itinerary.append({
                    "action": "meet",
                    "location": friend_locations[friend_index],
                    "person": friend_names[friend_index],
                    "start_time": format_time(start_time),
                    "end_time": format_time(end_time)
                })
        output = {"itinerary": itinerary}
        print(json.dumps(output))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()