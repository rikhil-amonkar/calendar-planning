import json
from z3 import *

def format_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    opt = Optimize()
    
    # Travel times in minutes between locations
    travel = {
        ("Bayview", "North Beach"): 21,
        ("Bayview", "Presidio"): 31,
        ("Bayview", "Haight-Ashbury"): 19,
        ("Bayview", "Union Square"): 17,
        ("North Beach", "Bayview"): 22,
        ("North Beach", "Presidio"): 17,
        ("North Beach", "Haight-Ashbury"): 18,
        ("North Beach", "Union Square"): 7,
        ("Presidio", "Bayview"): 31,
        ("Presidio", "North Beach"): 18,
        ("Presidio", "Haight-Ashbury"): 15,
        ("Presidio", "Union Square"): 22,
        ("Haight-Ashbury", "Bayview"): 18,
        ("Haight-Ashbury", "North Beach"): 19,
        ("Haight-Ashbury", "Presidio"): 15,
        ("Haight-Ashbury", "Union Square"): 17,
        ("Union Square", "Bayview"): 15,
        ("Union Square", "North Beach"): 10,
        ("Union Square", "Presidio"): 24,
        ("Union Square", "Haight-Ashbury"): 18
    }
    
    # Starting at Bayview at 9:00AM (in minutes)
    initial_location = "Bayview"
    initial_time = 9 * 60  # 9:00 AM
    
    # Friend meeting definitions
    # Times are represented in minutes after midnight.
    # For example, 13:45 is 13*60 + 45 = 825.
    friends = [
        {"name": "Barbara", "location": "North Beach", "avail_start": 13 * 60 + 45, "avail_end": 20 * 60 + 15, "min_duration": 60},
        {"name": "Margaret", "location": "Presidio", "avail_start": 10 * 60 + 15, "avail_end": 15 * 60 + 15, "min_duration": 30},
        {"name": "Kevin", "location": "Haight-Ashbury", "avail_start": 20 * 60, "avail_end": 20 * 60 + 45, "min_duration": 30},
        {"name": "Kimberly", "location": "Union Square", "avail_start": 7 * 60 + 45, "avail_end": 16 * 60 + 45, "min_duration": 30}
    ]
    
    # For each friend, create decision variables for whether to schedule a meeting,
    # as well as start and end times for the meeting.
    for friend in friends:
        friend["sched"] = Bool(f"sched_{friend['name']}")
        friend["start"] = Int(f"start_{friend['name']}")
        friend["end"] = Int(f"end_{friend['name']}")
        
        # If a meeting is scheduled, enforce the friend’s availability window,
        # the minimum meeting duration, and that you can get there from Bayview.
        opt.add(Implies(friend["sched"], friend["start"] >= friend["avail_start"]))
        opt.add(Implies(friend["sched"], friend["start"] >= initial_time + travel[(initial_location, friend["location"])]))
        opt.add(Implies(friend["sched"], friend["end"] <= friend["avail_end"]))
        opt.add(Implies(friend["sched"], friend["end"] - friend["start"] >= friend["min_duration"]))
    
    # Add disjunctive scheduling constraints for every pair of meetings.
    # If you schedule both meetings, then either one must finish (plus travel time to the next location)
    # before the other begins.
    for i in range(len(friends)):
        for j in range(i + 1, len(friends)):
            f1 = friends[i]
            f2 = friends[j]
            opt.add(
                Implies(
                    And(f1["sched"], f2["sched"]),
                    Or(
                        f1["end"] + travel[(f1["location"], f2["location"])] <= f2["start"],
                        f2["end"] + travel[(f2["location"], f1["location"])] <= f1["start"]
                    )
                )
            )
    
    # Objective: maximize the number of meetings scheduled.
    total_meetings = Sum([If(friend["sched"], 1, 0) for friend in friends])
    opt.maximize(total_meetings)
    
    if opt.check() == sat:
        model = opt.model()
        scheduled_meetings = []
        for friend in friends:
            if is_true(model.evaluate(friend["sched"])):
                start_val = model.evaluate(friend["start"]).as_long()
                end_val = model.evaluate(friend["end"]).as_long()
                scheduled_meetings.append({
                    "person": friend["name"],
                    "location": friend["location"],
                    "start": start_val,
                    "end": end_val
                })
                
        # Sort the meetings by start time to reflect the itinerary order.
        scheduled_meetings.sort(key=lambda m: m["start"])
        
        itinerary = []
        for meeting in scheduled_meetings:
            itinerary.append({
                "action": "meet",
                "location": meeting["location"],
                "person": meeting["person"],
                "start_time": format_time(meeting["start"]),
                "end_time": format_time(meeting["end"])
            })
        
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print(json.dumps({"itinerary": []}, indent=2))

if __name__ == '__main__':
    main()