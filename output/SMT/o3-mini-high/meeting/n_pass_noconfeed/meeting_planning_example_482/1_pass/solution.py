from z3 import *
import json

def minutes_to_time_str(t):
    # Convert minutes from midnight to "H:MM" (24-hour format, no leading zero on hour)
    hour = t // 60
    minute = t % 60
    return f"{hour}:{minute:02d}"

def main():
    # Friend data: name, meeting location, availability window (in minutes from midnight), and minimum meeting duration (minutes)
    friends = [
        {"name": "Stephanie", "location": "Mission District", "avail_start": 8 * 60 + 15, "avail_end": 13 * 60 + 45, "min_duration": 90},
        {"name": "Sandra", "location": "Bayview", "avail_start": 13 * 60, "avail_end": 19 * 60 + 30, "min_duration": 15},
        {"name": "Richard", "location": "Pacific Heights", "avail_start": 7 * 60 + 15, "avail_end": 10 * 60 + 15, "min_duration": 75},
        {"name": "Brian", "location": "Russian Hill", "avail_start": 12 * 60 + 15, "avail_end": 16 * 60, "min_duration": 120},
        {"name": "Jason", "location": "Fisherman's Wharf", "avail_start": 8 * 60 + 30, "avail_end": 17 * 60 + 45, "min_duration": 60}
    ]

    # Travel times between locations (in minutes), note: these are directed.
    travel = {
        ("Haight-Ashbury", "Mission District"): 11,
        ("Haight-Ashbury", "Bayview"): 18,
        ("Haight-Ashbury", "Pacific Heights"): 12,
        ("Haight-Ashbury", "Russian Hill"): 17,
        ("Haight-Ashbury", "Fisherman's Wharf"): 23,
        ("Mission District", "Haight-Ashbury"): 12,
        ("Mission District", "Bayview"): 15,
        ("Mission District", "Pacific Heights"): 16,
        ("Mission District", "Russian Hill"): 15,
        ("Mission District", "Fisherman's Wharf"): 22,
        ("Bayview", "Haight-Ashbury"): 19,
        ("Bayview", "Mission District"): 13,
        ("Bayview", "Pacific Heights"): 23,
        ("Bayview", "Russian Hill"): 23,
        ("Bayview", "Fisherman's Wharf"): 25,
        ("Pacific Heights", "Haight-Ashbury"): 11,
        ("Pacific Heights", "Mission District"): 15,
        ("Pacific Heights", "Bayview"): 22,
        ("Pacific Heights", "Russian Hill"): 7,
        ("Pacific Heights", "Fisherman's Wharf"): 13,
        ("Russian Hill", "Haight-Ashbury"): 17,
        ("Russian Hill", "Mission District"): 16,
        ("Russian Hill", "Bayview"): 23,
        ("Russian Hill", "Pacific Heights"): 7,
        ("Russian Hill", "Fisherman's Wharf"): 7,
        ("Fisherman's Wharf", "Haight-Ashbury"): 22,
        ("Fisherman's Wharf", "Mission District"): 22,
        ("Fisherman's Wharf", "Bayview"): 26,
        ("Fisherman's Wharf", "Pacific Heights"): 12,
        ("Fisherman's Wharf", "Russian Hill"): 7
    }

    # You start your day at Haight-Ashbury at 9:00 AM (540 minutes)
    initial_location = "Haight-Ashbury"
    initial_time = 9 * 60

    # Maximum number of meeting slots equals the number of friends.
    n_slots = len(friends)

    # Use Optimize so we can maximize the number of meetings scheduled.
    opt = Optimize()

    # Create itinerary slots: each slot is an Int variable representing the friend index scheduled there,
    # or -1 if the slot is unused.
    itinerary = [Int(f"slot_{i}") for i in range(n_slots)]
    for i in range(n_slots):
        # Domain: -1 (unused) or 0..4 (friend index)
        opt.add(itinerary[i] >= -1, itinerary[i] <= n_slots - 1)

    # Enforce that there are no gaps: if a slot is unused (-1), then all subsequent slots must also be unused.
    for i in range(n_slots - 1):
        opt.add(If(itinerary[i] == -1, itinerary[i + 1] == -1, True))

    # Enforce that no friend is scheduled more than once.
    for i in range(n_slots):
        for j in range(i + 1, n_slots):
            opt.add(If(And(itinerary[i] != -1, itinerary[j] != -1), itinerary[i] != itinerary[j], True))

    # Count of scheduled meetings (to be maximized)
    scheduled_count = Sum([If(itinerary[i] == -1, 0, 1) for i in range(n_slots)])

    # Create variables for the start and end times (in minutes) for each meeting slot.
    start_vars = [Int(f"start_{i}") for i in range(n_slots)]
    end_vars = [Int(f"end_{i}") for i in range(n_slots)]

    # For each slot, if a friend is scheduled there, add constraints based on that friend's availability and minimum meeting duration.
    for i in range(n_slots):
        for fid in range(len(friends)):
            friend = friends[fid]
            # If slot i schedules friend fid then:
            opt.add(Implies(itinerary[i] == fid, start_vars[i] >= friend["avail_start"]))
            opt.add(Implies(itinerary[i] == fid, end_vars[i] <= friend["avail_end"]))
            opt.add(Implies(itinerary[i] == fid, end_vars[i] - start_vars[i] >= friend["min_duration"]))
        # If the slot is unused, set its start and end to 0 (dummy values)
        opt.add(Implies(itinerary[i] == -1, And(start_vars[i] == 0, end_vars[i] == 0)))
        # General non-negativity (if used, start must be before end)
        opt.add(start_vars[i] <= end_vars[i])

    # Add travel time constraints.
    # For the first scheduled slot: travel from the initial location to the friend’s location.
    # Since there are no gaps, the first slot (slot_0) is the first meeting if it is scheduled.
    for fid in range(len(friends)):
        friend = friends[fid]
        tt = travel.get((initial_location, friend["location"]), 0)
        opt.add(Implies(itinerary[0] == fid, initial_time + tt <= start_vars[0]))

    # For consecutive scheduled slots, ensure that the end time plus travel time from one meeting to the next is before the next meeting's start.
    for i in range(n_slots - 1):
        for fid1 in range(len(friends)):
            for fid2 in range(len(friends)):
                loc1 = friends[fid1]["location"]
                loc2 = friends[fid2]["location"]
                tt = travel.get((loc1, loc2), 0)
                opt.add(Implies(And(itinerary[i] == fid1, itinerary[i + 1] == fid2),
                                 end_vars[i] + tt <= start_vars[i + 1]))

    # Maximize the number of scheduled meetings.
    opt.maximize(scheduled_count)

    # Check for satisfiability and extract the model.
    if opt.check() == sat:
        model = opt.model()
        result_itinerary = []
        for i in range(n_slots):
            slot_val = model.evaluate(itinerary[i]).as_long()
            if slot_val != -1:
                friend = friends[slot_val]
                start_time = model.evaluate(start_vars[i]).as_long()
                end_time = model.evaluate(end_vars[i]).as_long()
                result_itinerary.append({
                    "action": "meet",
                    "location": friend["location"],
                    "person": friend["name"],
                    "start_time": minutes_to_time_str(start_time),
                    "end_time": minutes_to_time_str(end_time)
                })
        output = {"itinerary": result_itinerary}
        print(json.dumps(output, indent=2))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()