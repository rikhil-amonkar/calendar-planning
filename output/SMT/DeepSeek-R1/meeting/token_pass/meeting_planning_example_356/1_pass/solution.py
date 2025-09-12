from z3 import *
import json

def main():
    # Initialize solver
    s = Optimize()
    
    # Convert all times to minutes since 9:00 AM (540 minutes)
    start_time_total = 540  # 9:00 AM in minutes

    # Define location indices
    locations = ["Bayview", "North Beach", "Presidio", "Haight-Ashbury", "Union Square"]
    loc_index = {loc: idx for idx, loc in enumerate(locations)}
    
    # Travel time matrix (from [row] to [col])
    travel_times = [
        [0, 21, 31, 19, 17],  # Bayview
        [22, 0, 17, 18, 7],   # North Beach
        [31, 18, 0, 15, 22],  # Presidio
        [18, 19, 15, 0, 17],  # Haight-Ashbury
        [15, 10, 24, 18, 0]   # Union Square
    ]

    # Person data: [location, available_start, available_end, min_duration]
    people = {
        "Barbara": [loc_index["North Beach"], 13*60+45, 20*60+15, 60],
        "Margaret": [loc_index["Presidio"], 10*60+15, 15*60+15, 30],
        "Kevin": [loc_index["Haight-Ashbury"], 20*60, 20*60+45, 30],
        "Kimberly": [loc_index["Union Square"], 7*60+45, 16*60+45, 30]
    }

    # Create Z3 variables for each person's meeting start and end times
    starts = {name: Int(f"start_{name}") for name in people}
    ends = {name: Int(f"end_{name}") for name in people}
    meet_flags = {name: Bool(f"meet_{name}") for name in people}  # Whether we meet this person

    # Constraints for each person
    for name, (loc, avail_start, avail_end, min_dur) in people.items():
        # If we meet them, constraints apply
        s.add(Implies(meet_flags[name], starts[name] >= avail_start))
        s.add(Implies(meet_flags[name], ends[name] <= avail_end))
        s.add(Implies(meet_flags[name], ends[name] - starts[name] >= min_dur))
        # If not meeting, set times to 0
        s.add(Implies(Not(meet_flags[name]), starts[name] == 0))
        s.add(Implies(Not(meet_flags[name]), ends[name] == 0))

    # All meetings must be after arrival plus travel from Bayview
    for name in people:
        loc = people[name][0]
        travel_time = travel_times[0][loc]  # From Bayview to person's location
        s.add(Implies(meet_flags[name], starts[name] >= start_time_total + travel_time))

    # No overlapping meetings considering travel times
    names = list(people.keys())
    for i in range(len(names)):
        for j in range(i+1, len(names)):
            n1, n2 = names[i], names[j]
            loc1, loc2 = people[n1][0], people[n2][0]
            travel = travel_times[loc1][loc2]
            
            # Either n1 before n2 or n2 before n1, with travel time
            constraint = Or(
                And(meet_flags[n1], meet_flags[n2], ends[n1] + travel <= starts[n2]),
                And(meet_flags[n1], meet_flags[n2], ends[n2] + travel_times[loc2][loc1] <= starts[n1]),
                Not(meet_flags[n1]),
                Not(meet_flags[n2])
            )
            s.add(constraint)

    # Maximize number of meetings
    meeting_count = Sum([If(meet_flags[name], 1, 0) for name in people])
    s.maximize(meeting_count)

    # Solve and output
    if s.check() == sat:
        model = s.model()
        itinerary = []
        
        # Collect all meetings that happened
        meetings = []
        for name in people:
            if is_true(model.eval(meet_flags[name])):
                start_val = model.eval(starts[name]).as_long()
                end_val = model.eval(ends[name]).as_long()
                meetings.append({
                    "person": name,
                    "location": locations[people[name][0]],
                    "start": start_val,
                    "end": end_val
                })
        
        # Sort meetings by start time
        meetings.sort(key=lambda x: x["start"])
        
        # Convert to output format
        for meet in meetings:
            # Convert minutes to time strings
            start_min = meet["start"]
            end_min = meet["end"]
            start_str = f"{start_min//60}:{start_min%60:02d}"
            end_str = f"{end_min//60}:{end_min%60:02d}"
            itinerary.append({
                "action": "meet",
                "location": meet["location"],
                "person": meet["person"],
                "start_time": start_str,
                "end_time": end_str
            })
        
        print(json.dumps({"itinerary": itinerary}, indent=2))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()