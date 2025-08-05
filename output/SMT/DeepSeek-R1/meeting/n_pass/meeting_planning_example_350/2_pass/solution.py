from z3 import *
import json

def main():
    # Convert times to minutes since 9:00 AM
    # Mary: 10:00AM to 7:00PM -> 60 to 600 minutes
    # Lisa: 8:30PM to 10:00PM -> 690 to 780 minutes (since 8:30PM is 11.5 hours after 9AM -> 11.5*60 = 690)
    # Betty: 7:15AM to 5:15PM -> Betty is available before 9AM? We start at 9AM, so from 0 minutes (9:00AM) to 495 minutes (5:15PM is 8.25 hours after 9AM -> 8.25*60=495)
    # Charles: 11:15AM to 3:00PM -> 135 to 360 minutes (11:15AM is 2.25 hours after 9AM -> 2.25*60=135; 3PM is 6 hours after 9AM -> 6*60=360)
    friends = [
        ('Mary', 'Pacific Heights', 60, 600, 45),    # 10:00AM to 7:00PM, min 45 minutes
        ('Lisa', 'Mission District', 690, 780, 75),  # 8:30PM to 10:00PM, min 75 minutes
        ('Betty', 'Haight-Ashbury', 0, 495, 90),     # 9:00AM to 5:15PM (but available from 7:15AM, but we start at 9:00AM), min 90 minutes
        ('Charles', 'Financial District', 135, 360, 120)  # 11:15AM to 3:00PM, min 120 minutes
    ]
    
    # Travel times dictionary: from -> to -> minutes
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
    
    # Create variables for each friend
    meet_vars = [Bool(f"meet_{name}") for (name, *_) in friends]
    start_vars = [Int(f"start_{name}") for (name, *_) in friends]
    pos_vars = [Int(f"pos_{name}") for (name, *_) in friends]  # position in the sequence (if met)
    
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
        # If not meeting, set position to -1 (to avoid interfering with distinct)
        s.add(Implies(Not(meet_vars[idx]), pos_vars[idx] == -1))
    
    # Distinct positions for met friends (non-met are set to -1, so distinct as long as met friends have distinct positions)
    s.add(Distinct([pos_vars[i] for i in range(len(friends))]))
    
    # Let n = total_meetings
    n = total_meetings
    # For each i in [0, 3], if i < n then there must be a meeting with position i
    for i in range(4):
        # We create a condition: if i is less than the total number of meetings, then at least one friend has position i (and is met)
        s.add(Implies(i < n, Or([And(meet_vars[j], pos_vars[j] == i) for j in range(len(friends)))))
    
    # Constraints for the first meeting (position 0): must account for travel from Bayview
    for idx, (name, loc, *_) in enumerate(friends):
        s.add(Implies(And(meet_vars[idx], pos_vars[idx] == 0),
                      start_vars[idx] >= travel_times['Bayview'][loc]))
    
    # Constraints for consecutive meetings: if two meetings are adjacent in the sequence (positions p and p+1), account for travel
    for i in range(len(friends)):
        for j in range(len(friends)):
            if i == j:
                continue
            name_i, loc_i, *rest_i = friends[i]
            name_j, loc_j, *rest_j = friends[j]
            # If both are met and j comes right after i in the sequence (i has position p, j has position p+1)
            cond = And(meet_vars[i], meet_vars[j], pos_vars[j] == pos_vars[i] + 1)
            # Then the start time of j must be at least the end time of i plus travel time
            s.add(Implies(cond, 
                         start_vars[i] + rest_i[3] + travel_times[loc_i][loc_j] <= start_vars[j]))
    
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