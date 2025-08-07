from z3 import *
import json

def main():
    # Map location names to indices
    location_map = {
        "Financial District": 0,
        "Fisherman's Wharf": 1,
        "Presidio": 2,
        "Bayview": 3,
        "Haight-Ashbury": 4,
        "Russian Hill": 5,
        "The Castro": 6,
        "Marina District": 7,
        "Richmond District": 8,
        "Union Square": 9,
        "Sunset District": 10
    }

    # Travel time matrix (11x11)
    travel_time = [
        [0, 10, 22, 19, 19, 11, 20, 15, 21, 9, 30],
        [11, 0, 17, 26, 22, 7, 27, 9, 18, 13, 27],
        [23, 19, 0, 31, 15, 14, 21, 11, 7, 22, 15],
        [19, 25, 32, 0, 19, 23, 19, 27, 25, 18, 23],
        [21, 23, 15, 18, 0, 17, 6, 17, 10, 19, 15],
        [11, 7, 14, 23, 17, 0, 21, 7, 14, 10, 23],
        [21, 24, 20, 19, 6, 18, 0, 21, 16, 19, 17],
        [17, 10, 10, 27, 16, 8, 22, 0, 11, 16, 19],
        [22, 18, 7, 27, 10, 13, 16, 9, 0, 21, 11],
        [9, 15, 24, 15, 18, 13, 17, 18, 20, 0, 27],
        [30, 29, 16, 22, 15, 24, 17, 21, 12, 30, 0]
    ]

    # Friend data: name, location, available start, available end, min duration
    friends = [
        {"name": "Mark", "location": "Fisherman's Wharf", "avail_start": "8:15AM", "avail_end": "10:00AM", "min_dur": 30},
        {"name": "Stephanie", "location": "Presidio", "avail_start": "12:15PM", "avail_end": "3:00PM", "min_dur": 75},
        {"name": "Betty", "location": "Bayview", "avail_start": "7:15AM", "avail_end": "8:30PM", "min_dur": 15},
        {"name": "Lisa", "location": "Haight-Ashbury", "avail_start": "3:30PM", "avail_end": "6:30PM", "min_dur": 45},
        {"name": "William", "location": "Russian Hill", "avail_start": "6:45PM", "avail_end": "8:00PM", "min_dur": 60},
        {"name": "Brian", "location": "The Castro", "avail_start": "9:15AM", "avail_end": "1:15PM", "min_dur": 30},
        {"name": "Joseph", "location": "Marina District", "avail_start": "10:45AM", "avail_end": "3:00PM", "min_dur": 90},
        {"name": "Ashley", "location": "Richmond District", "avail_start": "9:45AM", "avail_end": "11:15AM", "min_dur": 45},
        {"name": "Patricia", "location": "Union Square", "avail_start": "4:30PM", "avail_end": "8:00PM", "min_dur": 120},
        {"name": "Karen", "location": "Sunset District", "avail_start": "4:30PM", "avail_end": "10:00PM", "min_dur": 105}
    ]

    # Convert time strings to minutes since midnight
    def time_to_minutes(time_str):
        if time_str.endswith("AM"):
            time_str = time_str[:-2].strip()
            if ":" in time_str:
                hours, minutes = time_str.split(":")
                hours = int(hours)
                if hours == 12:  # 12AM is 0 hours
                    hours = 0
            else:
                hours = int(time_str)
                minutes = 0
        elif time_str.endswith("PM"):
            time_str = time_str[:-2].strip()
            if ":" in time_str:
                hours, minutes = time_str.split(":")
                hours = int(hours)
                if hours != 12:
                    hours += 12
            else:
                hours = int(time_str)
                if hours != 12:
                    hours += 12
                minutes = 0
        else:
            raise ValueError(f"Invalid time format: {time_str}")
        return int(hours) * 60 + int(minutes)

    # Convert friend data to minutes
    for friend in friends:
        friend["avail_start_min"] = time_to_minutes(friend["avail_start"])
        friend["avail_end_min"] = time_to_minutes(friend["avail_end"])
        friend["loc_index"] = location_map[friend["location"]]

    # Create Z3 solver
    opt = Optimize()
    n_friends = len(friends)
    
    # Decision variables
    meet = [Bool(f'meet_{i}') for i in range(n_friends)]
    start = [Int(f'start_{i}') for i in range(n_friends)]
    
    # Fixed start at Financial District at 9:00 AM (540 minutes)
    start_s = 540
    loc_s = 0
    
    # Constraints for each friend
    for i in range(n_friends):
        # If meeting the friend, the start time must be within their availability window
        opt.add(Implies(meet[i], start[i] >= friend["avail_start_min"]))
        opt.add(Implies(meet[i], start[i] + friends[i]["min_dur"] <= friends[i]["avail_end_min"]))
    
    # Create a list for all meetings (including the start)
    meetings = []
    # Meeting 0: the start
    meetings.append( (start_s, start_s, loc_s) )  # (start, end, location)
    # Meetings for friends
    for i in range(n_friends):
        meetings.append( (start[i], start[i] + friends[i]["min_dur"], friends[i]["loc_index"]) )
    
    # Active flags: the start is always active, then the meet flags for friends
    active_flags = [True]  # for the start
    active_flags.extend(meet)  # for the friends
    
    # Disjunctive constraints for every pair of meetings
    n_meetings = len(meetings)
    for i in range(n_meetings):
        for j in range(i+1, n_meetings):
            s1, e1, l1 = meetings[i]
            s2, e2, l2 = meetings[j]
            active_i = active_flags[i]
            active_j = active_flags[j]
            # Both meetings must be active
            condition = And(active_i, active_j)
            # Travel times
            travel_ij = travel_time[l1][l2]
            travel_ji = travel_time[l2][l1]
            # Either meeting i ends and travel to j before meeting j starts, or vice versa
            opt.add(Implies(condition, Or(e1 + travel_ij <= s2, e2 + travel_ji <= s1)))
    
    # Maximize the number of meetings
    total_meetings = Sum([If(meet[i], 1, 0) for i in range(n_friends)])
    opt.maximize(total_meetings)
    
    # Check for a solution
    if opt.check() == sat:
        m = opt.model()
        itinerary = []
        for i in range(n_friends):
            if m.eval(meet[i]):
                start_val = m.eval(start[i])
                start_minutes = start_val.as_long()
                end_minutes = start_minutes + friends[i]["min_dur"]
                # Convert minutes to time string (HH:MM)
                def format_time(minutes):
                    hours = minutes // 60
                    mins = minutes % 60
                    return f"{hours:02d}:{mins:02d}"
                itinerary.append({
                    "action": "meet",
                    "person": friends[i]["name"],
                    "start_time": format_time(start_minutes),
                    "end_time": format_time(end_minutes)
                })
        # Sort itinerary by start_time
        itinerary.sort(key=lambda x: x['start_time'])
        print("SOLUTION:")
        print(json.dumps({"itinerary": itinerary}))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()