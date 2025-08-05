from z3 import *
import json

def main():
    # Define friends data: (name, location, available_start (min), available_end (min), min_duration (min))
    friends = [
        ('Mary', 'Pacific Heights', 60, 600, 45),
        ('Lisa', 'Mission District', 690, 780, 75),
        ('Betty', 'Haight-Ashbury', 0, 495, 90),
        ('Charles', 'Financial District', 135, 360, 120)
    ]
    
    # Travel times dictionary
    travel_times = {
        "Bayview": {
            "Pacific Heights": 23,
            "Mission District": 13,
            "Haight-Ashbury": 19,
            "Financial District": 19
        },
        "Pacific Heights": {
            "Bayview": 22,
            "Mission District": 15,
            "Haight-Ashbury": 11,
            "Financial District": 13
        },
        "Mission District": {
            "Bayview": 15,
            "Pacific Heights": 16,
            "Haight-Ashbury": 12,
            "Financial District": 17
        },
        "Haight-Ashbury": {
            "Bayview": 18,
            "Pacific Heights": 12,
            "Mission District": 11,
            "Financial District": 21
        },
        "Financial District": {
            "Bayview": 19,
            "Pacific Heights": 13,
            "Mission District": 17,
            "Haight-Ashbury": 19
        }
    }
    
    s = Optimize()
    
    # Create variables for each friend: whether we meet, start time, and position in the sequence
    meet_vars = [Bool(f"meet_{name}") for (name, *_) in friends]
    start_vars = [Int(f"start_{name}") for (name, *_) in friends]
    pos_vars = [Int(f"pos_{name}") for (name, *_) in friends]
    
    # Total meetings is the sum of meet_vars
    total_meetings = Sum([If(meet_vars[i], 1, 0) for i in range(len(friends))])
    
    # Constraints for each friend
    for idx, (name, loc, avail_start, avail_end, dur) in enumerate(friends):
        # If meeting, ensure within availability and set position between 0 and 3
        s.add(Implies(meet_vars[idx], 
                      And(start_vars[idx] >= avail_start, 
                          start_vars[idx] + dur <= avail_end,
                          pos_vars[idx] >= 0,
                          pos_vars[idx] < 4)))
    
    # Distinct positions for met friends (set to -1 if not met)
    s.add(Distinct([If(meet_vars[i], pos_vars[i], -1) for i in range(len(friends))]))
    
    # Ensure positions for met friends are consecutive starting at 0
    min_pos = Int('min_pos')
    max_pos = Int('max_pos')
    met_positions = [If(meet_vars[i], pos_vars[i], 100000) for i in range(len(friends))]
    met_positions_for_max = [If(meet_vars[i], pos_vars[i], -1) for i in range(len(friends))]
    s.add(min_pos == Min(met_positions))
    s.add(max_pos == Max(met_positions_for_max))
    s.add(If(total_meetings > 0, And(min_pos == 0, max_pos == total_meetings - 1), True))
    s.add(If(total_meetings > 0, total_meetings == (max_pos - min_pos + 1), True))
    
    # Constraints for the first meeting: travel from Bayview to the first location
    for idx, (name, loc, *_) in enumerate(friends):
        s.add(Implies(And(meet_vars[idx], pos_vars[idx] == 0),
                      start_vars[idx] >= travel_times['Bayview'][loc]))
    
    # Constraints for consecutive meetings: travel time between locations
    for i in range(len(friends)):
        for j in range(len(friends)):
            if i == j:
                continue
            name_i, loc_i, *rest_i = friends[i]
            name_j, loc_j, *rest_j = friends[j]
            # If both are met and j comes right after i in the sequence
            cond = And(meet_vars[i], meet_vars[j], pos_vars[j] == pos_vars[i] + 1)
            # Then the start time of j must be at least the end time of i plus travel time
            s.add(Implies(cond, 
                         start_vars[i] + friends[i][4] + travel_times[loc_i][loc_j] <= start_vars[j]))
    
    # Maximize the number of meetings
    s.maximize(total_meetings)
    
    # Check and get the model
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for idx, (name, loc, avail_start, avail_end, dur) in enumerate(friends):
            if m.evaluate(meet_vars[idx]):
                start_val = m.evaluate(start_vars[idx])
                start_minutes = start_val.as_long()
                total_minutes_end = start_minutes + dur
                # Convert to absolute time (starting at 9:00 AM)
                hour_start = 9 + (start_minutes // 60)
                minute_start = start_minutes % 60
                hour_end = 9 + (total_minutes_end // 60)
                minute_end = total_minutes_end % 60
                start_str = f"{hour_start:02d}:{minute_start:02d}"
                end_str = f"{hour_end:02d}:{minute_end:02d}"
                itinerary.append({
                    "action": "meet",
                    "person": name,
                    "start_time": start_str,
                    "end_time": end_str
                })
        # Sort by start time
        itinerary.sort(key=lambda x: x['start_time'])
        print("SOLUTION:")
        print(json.dumps({"itinerary": itinerary}))
    else:
        print("SOLUTION:")
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()