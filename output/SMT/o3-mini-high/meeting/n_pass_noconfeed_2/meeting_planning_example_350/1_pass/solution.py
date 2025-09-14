from z3 import Int, Bool, Optimize, If, And, Or, Implies, Not
import json

def format_time(total_minutes):
    hour = total_minutes // 60
    minute = total_minutes % 60
    return f"{hour}:{minute:02d}"

def main():
    opt = Optimize()
    
    # Base arrival: You arrive at Bayview at 9:00 (9*60 = 540 minutes)
    base_time = 540
    base_location = "Bayview"
    
    # Friend meeting data with availability windows (in minutes) and min meeting durations.
    # Times are minutes after midnight.
    friends = [
        {
            "name": "Mary",
            "location": "Pacific Heights",
            "avail_start": 600,   # 10:00
            "avail_end": 1140,    # 19:00
            "duration": 45
        },
        {
            "name": "Lisa",
            "location": "Mission District",
            "avail_start": 1230,  # 20:30
            "avail_end": 1320,    # 22:00
            "duration": 75
        },
        {
            "name": "Betty",
            "location": "Haight-Ashbury",
            "avail_start": 435,   # 7:15
            "avail_end": 1035,    # 17:15
            "duration": 90
        },
        {
            "name": "Charles",
            "location": "Financial District",
            "avail_start": 675,   # 11:15
            "avail_end": 900,     # 15:00
            "duration": 120
        }
    ]
    num_friends = len(friends)
    
    # Travel times (in minutes) between locations
    travel = {
        ( "Bayview", "Pacific Heights" ): 23,
        ( "Bayview", "Mission District" ): 13,
        ( "Bayview", "Haight-Ashbury" ): 19,
        ( "Bayview", "Financial District" ): 19,
        ( "Pacific Heights", "Bayview" ): 22,
        ( "Pacific Heights", "Mission District" ): 15,
        ( "Pacific Heights", "Haight-Ashbury" ): 11,
        ( "Pacific Heights", "Financial District" ): 13,
        ( "Mission District", "Bayview" ): 15,
        ( "Mission District", "Pacific Heights" ): 16,
        ( "Mission District", "Haight-Ashbury" ): 12,
        ( "Mission District", "Financial District" ): 17,
        ( "Haight-Ashbury", "Bayview" ): 18,
        ( "Haight-Ashbury", "Pacific Heights" ): 12,
        ( "Haight-Ashbury", "Mission District" ): 11,
        ( "Haight-Ashbury", "Financial District" ): 21,
        ( "Financial District", "Bayview" ): 19,
        ( "Financial District", "Pacific Heights" ): 13,
        ( "Financial District", "Mission District" ): 17,
        ( "Financial District", "Haight-Ashbury" ): 19
    }
    
    # Decision variables:
    # scheduled[i] is True if meeting with friend i is scheduled.
    scheduled = [Bool(f"scheduled_{i}") for i in range(num_friends)]
    # start_vars[i] and end_vars[i] mark start and end times (in minutes) for each meeting.
    start_vars = [Int(f"start_{i}") for i in range(num_friends)]
    end_vars = [Int(f"end_{i}") for i in range(num_friends)]
    
    # Add constraints for each friend meeting if it is scheduled.
    for i in range(num_friends):
        friend = friends[i]
        # When meeting is scheduled, meeting must:
        # - Start no earlier than friend available time and after you travel from Bayview.
        # - End no later than friend available end.
        # - Last at least the required duration.
        opt.add(Implies(scheduled[i],
                        And(
                            start_vars[i] >= friend["avail_start"],
                            start_vars[i] >= base_time + travel[(base_location, friend["location"])],
                            end_vars[i] <= friend["avail_end"],
                            end_vars[i] - start_vars[i] >= friend["duration"]
                        )))
        # If not scheduled, fix times to 0 (so they don't interfere with ordering constraints).
        opt.add(Implies(Not(scheduled[i]), start_vars[i] == 0))
        opt.add(Implies(Not(scheduled[i]), end_vars[i] == 0))
    
    # Add ordering constraints for any two scheduled meetings.
    # If both meeting i and meeting j are scheduled, then one must follow the other while accounting for travel time.
    for i in range(num_friends):
        for j in range(i+1, num_friends):
            friend_i = friends[i]
            friend_j = friends[j]
            travel_ij = travel[(friend_i["location"], friend_j["location"])]
            travel_ji = travel[(friend_j["location"], friend_i["location"])]
            opt.add(Implies(And(scheduled[i], scheduled[j]),
                        Or(
                            start_vars[j] >= end_vars[i] + travel_ij,
                            start_vars[i] >= end_vars[j] + travel_ji
                        )))
    
    # Objective: maximize the number of scheduled meetings.
    total_meetings = sum([If(scheduled[i], 1, 0) for i in range(num_friends)])
    opt.maximize(total_meetings)
    
    if opt.check() == 'sat':
        model = opt.model()
        
        # Gather scheduled meetings and sort by start time.
        meetings = []
        for i in range(num_friends):
            if model.evaluate(scheduled[i]):
                s_val = model.evaluate(start_vars[i]).as_long()
                e_val = model.evaluate(end_vars[i]).as_long()
                meetings.append({
                    "start": s_val,
                    "end": e_val,
                    "location": friends[i]["location"],
                    "person": friends[i]["name"]
                })
        meetings.sort(key=lambda x: x["start"])
        
        itinerary = []
        for m in meetings:
            itinerary.append({
                "action": "meet",
                "location": m["location"],
                "person": m["person"],
                "start_time": format_time(m["start"]),
                "end_time": format_time(m["end"])
            })
        
        output = {"itinerary": itinerary}
        print(json.dumps(output, indent=2))
    else:
        print(json.dumps({"itinerary": []}, indent=2))

if __name__ == '__main__':
    main()