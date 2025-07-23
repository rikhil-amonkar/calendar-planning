from z3 import *
import json

def solve_scheduling():
    # Initialize Z3 solver
    s = Optimize()

    # Define the friends and their availability
    friends = {
        "Laura": {"location": "The Castro", "start": "19:45", "end": "21:30", "min_duration": 105},
        "Daniel": {"location": "Golden Gate Park", "start": "21:15", "end": "21:45", "min_duration": 15},
        "William": {"location": "Embarcadero", "start": "07:00", "end": "09:00", "min_duration": 90},
        "Karen": {"location": "Russian Hill", "start": "14:30", "end": "19:45", "min_duration": 30},
        "Stephanie": {"location": "Nob Hill", "start": "07:30", "end": "09:30", "min_duration": 45},
        "Joseph": {"location": "Alamo Square", "start": "11:30", "end": "12:45", "min_duration": 15},
        "Kimberly": {"location": "North Beach", "start": "15:45", "end": "19:15", "min_duration": 30}
    }

    # Convert time strings to minutes since midnight
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    # Convert minutes back to time string
    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Initialize variables for each friend's meeting start and end times
    meeting_vars = {}
    for name in friends:
        start_var = Int(f"{name}_start")
        end_var = Int(f"{name}_end")
        meeting_vars[name] = {"start": start_var, "end": end_var}

    # Define travel times between locations
    travel_times = {
        ("Fisherman's Wharf", "The Castro"): 26,
        ("Fisherman's Wharf", "Golden Gate Park"): 25,
        ("Fisherman's Wharf", "Embarcadero"): 8,
        ("Fisherman's Wharf", "Russian Hill"): 7,
        ("Fisherman's Wharf", "Nob Hill"): 11,
        ("Fisherman's Wharf", "Alamo Square"): 20,
        ("Fisherman's Wharf", "North Beach"): 6,
        ("The Castro", "Golden Gate Park"): 11,
        ("The Castro", "Embarcadero"): 22,
        ("The Castro", "Russian Hill"): 18,
        ("The Castro", "Nob Hill"): 16,
        ("The Castro", "Alamo Square"): 8,
        ("The Castro", "North Beach"): 20,
        ("Golden Gate Park", "Embarcadero"): 25,
        ("Golden Gate Park", "Russian Hill"): 19,
        ("Golden Gate Park", "Nob Hill"): 20,
        ("Golden Gate Park", "Alamo Square"): 10,
        ("Golden Gate Park", "North Beach"): 24,
        ("Embarcadero", "Russian Hill"): 8,
        ("Embarcadero", "Nob Hill"): 10,
        ("Embarcadero", "Alamo Square"): 19,
        ("Embarcadero", "North Beach"): 5,
        ("Russian Hill", "Nob Hill"): 5,
        ("Russian Hill", "Alamo Square"): 15,
        ("Russian Hill", "North Beach"): 5,
        ("Nob Hill", "Alamo Square"): 11,
        ("Nob Hill", "North Beach"): 8,
        ("Alamo Square", "North Beach"): 15
    }

    # Add constraints for each friend's meeting time
    for name in friends:
        friend = friends[name]
        start_min = time_to_minutes(friend["start"])
        end_min = time_to_minutes(friend["end"])
        min_duration = friend["min_duration"]

        s.add(meeting_vars[name]["start"] >= start_min)
        s.add(meeting_vars[name]["end"] <= end_min)
        s.add(meeting_vars[name]["end"] - meeting_vars[name]["start"] >= min_duration)

    # Define meeting order and travel constraints
    all_friends = list(friends.keys())
    num_meetings = len(all_friends)
    
    # Create variables to track meeting order
    order = [Int(f"order_{i}") for i in range(num_meetings)]
    s.add(Distinct(order))
    for i in range(num_meetings):
        s.add(order[i] >= 0, order[i] < num_meetings)

    # Create variables for start and end times of each meeting in the sequence
    seq_start = [Int(f"seq_start_{i}") for i in range(num_meetings)]
    seq_end = [Int(f"seq_end_{i}") for i in range(num_meetings)]

    # Connect meeting variables to sequence variables
    for i in range(num_meetings):
        for j in range(num_meetings):
            s.add(Implies(order[i] == j, seq_start[i] == meeting_vars[all_friends[j]]["start"]))
            s.add(Implies(order[i] == j, seq_end[i] == meeting_vars[all_friends[j]]["end"]))

    # Add travel time constraints between consecutive meetings
    for i in range(num_meetings - 1):
        for j in range(num_meetings):
            for k in range(num_meetings):
                if j == k:
                    continue
                loc1 = friends[all_friends[j]]["location"]
                loc2 = friends[all_friends[k]]["location"]
                if (loc1, loc2) in travel_times:
                    travel = travel_times[(loc1, loc2)]
                    s.add(Implies(And(order[i] == j, order[i+1] == k),
                                seq_start[i+1] >= seq_end[i] + travel))

    # Start at Fisherman's Wharf at 9:00 AM (540 minutes)
    first_meeting = order[0]
    for j in range(num_meetings):
        loc = friends[all_friends[j]]["location"]
        travel = travel_times.get(("Fisherman's Wharf", loc), 0)
        s.add(Implies(first_meeting == j, seq_start[0] >= 540 + travel))

    # Ensure we can't meet William (7:00-9:00) since we start at 9:00
    s.add(meeting_vars["William"]["start"] == 0)
    s.add(meeting_vars["William"]["end"] == 0)

    # Maximize the number of meetings scheduled
    scheduled = [Int(f"scheduled_{i}") for i in range(num_meetings)]
    for i in range(num_meetings):
        s.add(scheduled[i] == If(seq_start[i] > 0, 1, 0))
    total_scheduled = Int("total_scheduled")
    s.add(total_scheduled == sum(scheduled))
    s.maximize(total_scheduled)

    # Check if the problem is satisfiable
    if s.check() == sat:
        m = s.model()
        itinerary = []
        
        # Get the scheduled meetings in order
        scheduled_order = sorted([(m[order[i]].as_long(), i) for i in range(num_meetings)])
        
        for idx, i in scheduled_order:
            name = all_friends[idx]
            start = m[seq_start[i]].as_long()
            end = m[seq_end[i]].as_long()
            if start > 0 and end > 0:
                itinerary.append({
                    "action": "meet",
                    "person": name,
                    "start_time": minutes_to_time(start),
                    "end_time": minutes_to_time(end)
                })
        
        output = {"itinerary": itinerary}
        print(json.dumps(output, indent=2))
    else:
        print("No valid schedule found")

solve_scheduling()