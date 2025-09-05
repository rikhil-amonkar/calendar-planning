from z3 import *
import json

def convert_time(minutes_offset):
    # Convert minutes offset (from 9:00) to 24-hour time string (e.g., "9:00", "13:30")
    total = 9 * 60 + minutes_offset
    hour = total // 60
    minute = total % 60
    return f"{hour}:{minute:02d}"

def main():
    # Friend meeting data; times are in minutes relative to 9:00AM.
    # For example, an availability start time of 0 means 9:00 AM.
    # Note: Rebecca is originally available from 8:45 but adjusted to 9:00.
    friends = [
        {"name": "Kevin",    "location": "Mission District",    "avail_start": 705, "avail_end": 765, "duration": 60},
        {"name": "Mark",     "location": "Fisherman's Wharf",   "avail_start": 495, "avail_end": 660, "duration": 90},
        {"name": "Jessica",  "location": "Russian Hill",        "avail_start": 0,   "avail_end": 360, "duration": 120},
        {"name": "Jason",    "location": "Marina District",     "avail_start": 375, "avail_end": 765, "duration": 120},
        {"name": "John",     "location": "North Beach",         "avail_start": 45,  "avail_end": 540, "duration": 15},
        {"name": "Karen",    "location": "Chinatown",           "avail_start": 465, "avail_end": 600, "duration": 75},
        {"name": "Sarah",    "location": "Pacific Heights",     "avail_start": 510, "avail_end": 555, "duration": 45},
        {"name": "Amanda",   "location": "The Castro",          "avail_start": 660, "avail_end": 735, "duration": 60},
        {"name": "Nancy",    "location": "Nob Hill",            "avail_start": 45,  "avail_end": 240, "duration": 45},
        {"name": "Rebecca",  "location": "Sunset District",     "avail_start": 0,   "avail_end": 360, "duration": 75},
    ]
    
    MAX_SLOTS = 10  # maximum number of meeting slots available

    # Travel times (in minutes) from Union Square to each friend's location.
    # Order corresponds to the same order as in the friends list.
    start_travel = [14, 15, 13, 18, 10, 7, 15, 17, 9, 27]

    # Travel times between friend locations (matrix 10x10).
    # The order of rows and columns corresponds to the order in the "friends" list.
    # For instance, travel_matrix[i][j] is the travel time from friends[i]["location"] to friends[j]["location"].
    travel_matrix = [
        # Kevin (Mission District)
        [0, 22, 15, 19, 17, 16, 16, 7, 12, 24],
        # Mark (Fisherman's Wharf)
        [22, 0, 7, 9, 6, 12, 12, 27, 11, 27],
        # Jessica (Russian Hill)
        [16, 7, 0, 7, 5, 9, 7, 21, 5, 23],
        # Jason (Marina District)
        [20, 10, 8, 0, 11, 15, 7, 22, 12, 19],
        # John (North Beach)
        [18, 5, 4, 9, 0, 6, 8, 23, 7, 27],
        # Karen (Chinatown)
        [17, 8, 7, 12, 3, 0, 10, 22, 9, 29],
        # Sarah (Pacific Heights)
        [15, 13, 7, 6, 9, 11, 0, 16, 8, 21],
        # Amanda (The Castro)
        [7, 24, 18, 21, 20, 22, 16, 0, 16, 17],
        # Nancy (Nob Hill)
        [13, 10, 5, 11, 8, 6, 8, 17, 0, 24],
        # Rebecca (Sunset District)
        [25, 29, 24, 21, 28, 30, 21, 17, 27, 0]
    ]

    # Initialize the Optimize solver.
    opt = Optimize()

    # Create variables for each slot.
    # "slots[s]" will store the friend index scheduled in slot s, or -1 if slot is empty.
    slots = [Int(f"slot_{s}") for s in range(MAX_SLOTS)]
    # "start_vars[s]" and "end_vars[s]" represent the scheduled start and end times (minutes from 9:00)
    start_vars = [Int(f"start_{s}") for s in range(MAX_SLOTS)]
    end_vars   = [Int(f"end_{s}")   for s in range(MAX_SLOTS)]

    # Domain constraints for each slot and meeting times.
    for s in range(MAX_SLOTS):
        # Slot value is either -1 (unused) or a valid friend index.
        opt.add(Or(slots[s] == -1, And(slots[s] >= 0, slots[s] < len(friends))))
        # Meeting times are non-negative.
        opt.add(start_vars[s] >= 0)
        opt.add(end_vars[s] >= 0)
        # If a slot is unused, set its meeting times to 0.
        opt.add(Implies(slots[s] == -1, And(start_vars[s] == 0, end_vars[s] == 0)))
    
    # Enforce that once a slot is empty, all subsequent slots are empty.
    for s in range(MAX_SLOTS - 1):
        opt.add(Implies(slots[s] == -1, slots[s+1] == -1))
    
    # Ensure that scheduled meetings (non -1 slots) are all distinct.
    for s in range(MAX_SLOTS):
        for t in range(s+1, MAX_SLOTS):
            opt.add(Implies(And(slots[s] != -1, slots[t] != -1), slots[s] != slots[t]))
    
    # For each slot, if a friend is scheduled then its meeting must obey the friend’s constraints.
    for s in range(MAX_SLOTS):
        for i in range(len(friends)):
            friend = friends[i]
            opt.add(Implies(slots[s] == i,
                And(
                    start_vars[s] >= friend["avail_start"],
                    end_vars[s]   <= friend["avail_end"],
                    end_vars[s] - start_vars[s] >= friend["duration"]
                )
            ))
    
    # Travel constraint for the very first meeting: account for travel from Union Square.
    for i in range(len(friends)):
        opt.add(Implies(slots[0] == i, start_vars[0] >= start_travel[i]))
    
    # For consecutive meetings, ensure there is enough travel time between meetings.
    for s in range(1, MAX_SLOTS):
        for i in range(len(friends)):
            for j in range(len(friends)):
                opt.add(Implies(And(slots[s-1] == j, slots[s] == i),
                    start_vars[s] >= end_vars[s-1] + travel_matrix[j][i]
                ))
    
    # Objective: maximize the total number of meetings scheduled.
    total_meetings = Sum([If(slots[s] != -1, 1, 0) for s in range(MAX_SLOTS)])
    opt.maximize(total_meetings)
    
    # Solve the scheduling problem.
    if opt.check() == sat:
        m = opt.model()
        itinerary = []
        # Build the itinerary from the scheduled slots in order.
        for s in range(MAX_SLOTS):
            if m.evaluate(slots[s]).as_long() == -1:
                break
            friend_idx = m.evaluate(slots[s]).as_long()
            friend = friends[friend_idx]
            start_time_val = m.evaluate(start_vars[s]).as_long()
            end_time_val = m.evaluate(end_vars[s]).as_long()
            itinerary.append({
                "action": "meet",
                "location": friend["location"],
                "person": friend["name"],
                "start_time": convert_time(start_time_val),
                "end_time": convert_time(end_time_val)
            })
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()