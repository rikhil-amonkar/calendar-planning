import json
from z3 import *

def convert_time(t):
    # t is minutes after 9:00; add 9*60 to get minutes since midnight.
    total_minutes = t + 9 * 60
    hour = total_minutes // 60
    minute = total_minutes % 60
    return f"{hour}:{minute:02d}"

def main():
    # Friend data: (name, location, available_start, available_end, minimum_duration)
    # Times are measured in minutes after 9:00.
    friends = [
        ("Sarah", "Haight-Ashbury", 480, 750, 105),         # 17:00 to 21:30
        ("Patricia", "Sunset District", 480, 645, 45),        # 17:00 to 19:45
        ("Matthew", "Marina District", 15, 180, 15),          # 9:15 to 12:00
        ("Joseph", "Financial District", 315, 585, 30),       # 14:15 to 18:45
        ("Robert", "Union Square", 75, 765, 15)               # 10:15 to 21:45
    ]
    n = len(friends)
    
    # Base travel times from Golden Gate Park to each location.
    base_travel = {
        "Haight-Ashbury": 7,
        "Sunset District": 10,
        "Marina District": 16,
        "Financial District": 26,
        "Union Square": 22
    }
    
    # Travel times between districts (in minutes).
    travel_times = {
        ("Haight-Ashbury", "Sunset District"): 15,
        ("Haight-Ashbury", "Marina District"): 17,
        ("Haight-Ashbury", "Financial District"): 21,
        ("Haight-Ashbury", "Union Square"): 17,
        
        ("Sunset District", "Haight-Ashbury"): 15,
        ("Sunset District", "Marina District"): 21,
        ("Sunset District", "Financial District"): 30,
        ("Sunset District", "Union Square"): 30,
        
        ("Marina District", "Haight-Ashbury"): 16,
        ("Marina District", "Sunset District"): 19,
        ("Marina District", "Financial District"): 17,
        ("Marina District", "Union Square"): 16,
        
        ("Financial District", "Haight-Ashbury"): 19,
        ("Financial District", "Sunset District"): 31,
        ("Financial District", "Marina District"): 15,
        ("Financial District", "Union Square"): 9,
        
        ("Union Square", "Haight-Ashbury"): 18,
        ("Union Square", "Sunset District"): 26,
        ("Union Square", "Marina District"): 18,
        ("Union Square", "Financial District"): 9
    }
    
    # Create an optimizer instance.
    opt = Optimize()
    
    # Decision variables for each friend:
    # scheduled[i] is True if we schedule a meeting with friend i.
    # start_vars[i] and end_vars[i] represent the start and end times (in minutes after 9:00) for the meeting.
    scheduled = [Bool(f"scheduled_{i}") for i in range(n)]
    start_vars = [Int(f"start_{i}") for i in range(n)]
    end_vars   = [Int(f"end_{i}") for i in range(n)]
    
    # Add constraints for each friend meeting.
    for i, (name, location, avail_start, avail_end, min_duration) in enumerate(friends):
        # If meeting is scheduled, then its start and end must lie within the available window.
        opt.add(Implies(scheduled[i], start_vars[i] >= avail_start))
        opt.add(Implies(scheduled[i], end_vars[i] <= avail_end))
        opt.add(Implies(scheduled[i], end_vars[i] - start_vars[i] >= min_duration))
        # Even if it is the first meeting, you cannot arrive earlier than directly traveling from Golden Gate Park.
        opt.add(Implies(scheduled[i], start_vars[i] >= base_travel[location]))
    
    # For every pair of scheduled meetings, ensure that they do not overlap and that travel times between locations are respected.
    for i in range(n):
        for j in range(i + 1, n):
            loc_i = friends[i][1]
            loc_j = friends[j][1]
            t_ij = travel_times.get((loc_i, loc_j), 0)
            t_ji = travel_times.get((loc_j, loc_i), 0)
            # If both meetings are scheduled, then either i comes before j (with sufficient travel time)
            # or j comes before i.
            opt.add(Implies(And(scheduled[i], scheduled[j]),
                            Or(end_vars[i] + t_ij <= start_vars[j],
                               end_vars[j] + t_ji <= start_vars[i])))
    
    # Objective: maximize the number of scheduled meetings.
    total_meetings = Sum([If(scheduled[i], 1, 0) for i in range(n)])
    opt.maximize(total_meetings)
    
    # Check for satisfiability and get the model.
    if opt.check() == sat:
        model = opt.model()
        meetings = []
        # Collect scheduled meetings with their times.
        for i, (name, location, avail_start, avail_end, min_duration) in enumerate(friends):
            if is_true(model.evaluate(scheduled[i])):
                s_time = model.evaluate(start_vars[i]).as_long()
                e_time = model.evaluate(end_vars[i]).as_long()
                meetings.append({
                    "person": name,
                    "location": location,
                    "start": s_time,
                    "end": e_time
                })
        # Sort meetings in chronological order by start time.
        meetings.sort(key=lambda m: m["start"])
        
        # Build the itinerary in the required JSON format.
        itinerary = []
        for meeting in meetings:
            itinerary.append({
                "action": "meet",
                "location": meeting["location"],
                "person": meeting["person"],
                "start_time": convert_time(meeting["start"]),
                "end_time": convert_time(meeting["end"])
            })
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()