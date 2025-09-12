import z3
import json

def main():
    # Define travel times as a nested dictionary
    travel_times = {
        "Fisherman's Wharf": {
            "Bayview": 26,
            "Golden Gate Park": 25,
            "Nob Hill": 11,
            "Marina District": 9,
            "Embarcadero": 8
        },
        "Bayview": {
            "Fisherman's Wharf": 25,
            "Golden Gate Park": 22,
            "Nob Hill": 20,
            "Marina District": 25,
            "Embarcadero": 19
        },
        "Golden Gate Park": {
            "Fisherman's Wharf": 24,
            "Bayview": 23,
            "Nob Hill": 20,
            "Marina District": 16,
            "Embarcadero": 25
        },
        "Nob Hill": {
            "Fisherman's Wharf": 11,
            "Bayview": 19,
            "Golden Gate Park": 17,
            "Marina District": 11,
            "Embarcadero": 9
        },
        "Marina District": {
            "Fisherman's Wharf": 10,
            "Bayview": 27,
            "Golden Gate Park": 18,
            "Nob Hill": 12,
            "Embarcadero": 14
        },
        "Embarcadero": {
            "Fisherman's Wharf": 6,
            "Bayview": 21,
            "Golden Gate Park": 25,
            "Nob Hill": 10,
            "Marina District": 12
        }
    }

    # Convert all times to minutes since 9:00 AM (540 minutes from midnight)
    base_time = 9 * 60
    constraints = [
        {"name": "Thomas", "location": "Bayview", "start": 15*60+30 - base_time, "end": 18*60+30 - base_time, "min_duration": 120},
        {"name": "Stephanie", "location": "Golden Gate Park", "start": 18*60+30 - base_time, "end": 21*60+45 - base_time, "min_duration": 30},
        {"name": "Laura", "location": "Nob Hill", "start": max(8*60+45 - base_time, 0), "end": 16*60+15 - base_time, "min_duration": 30},
        {"name": "Betty", "location": "Marina District", "start": 18*60+45 - base_time, "end": 21*60+45 - base_time, "min_duration": 45},
        {"name": "Patricia", "location": "Embarcadero", "start": 17*60+30 - base_time, "end": 22*60 - base_time, "min_duration": 45}
    ]

    # Initialize Z3 variables
    s = z3.Solver()
    opt = z3.Optimize()

    # Create variables for each meeting: start, end, and a boolean for whether it's scheduled
    meeting_vars = []
    for i, constr in enumerate(constraints):
        start_var = z3.Int(f"start_{i}")
        end_var = z3.Int(f"end_{i}")
        scheduled_var = z3.Bool(f"scheduled_{i}")
        meeting_vars.append({
            "name": constr["name"],
            "location": constr["location"],
            "start": start_var,
            "end": end_var,
            "scheduled": scheduled_var,
            "min_duration": constr["min_duration"],
            "window_start": constr["start"],
            "window_end": constr["end"]
        })

    # Current location and time (start at Fisherman's Wharf at time 0)
    current_location = "Fisherman's Wharf"
    current_time = 0

    # Add constraints for each meeting
    for mtg in meeting_vars:
        # If scheduled, meeting must be within availability window and have minimum duration
        s.add(z3.Implies(mtg["scheduled"], 
                         z3.And(mtg["start"] >= mtg["window_start"],
                                mtg["end"] <= mtg["window_end"],
                                mtg["end"] - mtg["start"] >= mtg["min_duration"])))
        # If not scheduled, set start and end to -1 (invalid)
        s.add(z3.Implies(z3.Not(mtg["scheduled"]), 
                         z3.And(mtg["start"] == -1, mtg["end"] == -1)))

    # Constraint: meetings must not overlap and account for travel time
    for i in range(len(meeting_vars)):
        for j in range(i + 1, len(meeting_vars)):
            mtg1 = meeting_vars[i]
            mtg2 = meeting_vars[j]
            # If both are scheduled, one must start after the other ends plus travel time
            travel_time1 = travel_times[mtg1["location"]][mtg2["location"]]
            travel_time2 = travel_times[mtg2["location"]][mtg1["location"]]
            s.add(z3.Implies(z3.And(mtg1["scheduled"], mtg2["scheduled"]),
                             z3.Or(mtg2["start"] >= mtg1["end"] + travel_time1,
                                   mtg1["start"] >= mtg2["end"] + travel_time2)))

    # Constraint: first meeting must start after travel from Fisherman's Wharf
    for mtg in meeting_vars:
        travel_time = travel_times[current_location][mtg["location"]]
        s.add(z3.Implies(mtg["scheduled"], mtg["start"] >= current_time + travel_time))

    # Maximize the number of scheduled meetings
    scheduled_count = z3.Sum([z3.If(mtg["scheduled"], 1, 0) for mtg in meeting_vars])
    opt.add(s)
    opt.maximize(scheduled_count)

    # Check satisfiability
    if opt.check() == z3.sat:
        model = opt.model()
        itinerary = []
        for mtg in meeting_vars:
            if model.eval(mtg["scheduled"]):
                start_val = model.eval(mtg["start"]).as_long()
                end_val = model.eval(mtg["end"]).as_long()
                # Convert back to absolute time (minutes from midnight)
                abs_start = base_time + start_val
                abs_end = base_time + end_val
                hours_start = abs_start // 60
                minutes_start = abs_start % 60
                hours_end = abs_end // 60
                minutes_end = abs_end % 60
                start_str = f"{hours_start}:{minutes_start:02d}"
                end_str = f"{hours_end}:{minutes_end:02d}"
                itinerary.append({
                    "action": "meet",
                    "location": mtg["location"],
                    "person": mtg["name"],
                    "start_time": start_str,
                    "end_time": end_str
                })
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: x["start_time"])
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()