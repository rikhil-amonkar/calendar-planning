from z3 import *
import json
from collections import defaultdict

def solve_scheduling_problem():
    # Initialize Z3 solver
    opt = Optimize()

    # Define locations and travel times
    travel_times = {
        ("Chinatown", "Embarcadero"): 5,
        ("Chinatown", "Pacific Heights"): 10,
        ("Chinatown", "Russian Hill"): 7,
        ("Chinatown", "Haight-Ashbury"): 19,
        ("Chinatown", "Golden Gate Park"): 23,
        ("Chinatown", "Fisherman's Wharf"): 8,
        ("Chinatown", "Sunset District"): 29,
        ("Chinatown", "The Castro"): 22,
        ("Embarcadero", "Chinatown"): 7,
        ("Embarcadero", "Pacific Heights"): 11,
        ("Embarcadero", "Russian Hill"): 8,
        ("Embarcadero", "Haight-Ashbury"): 21,
        ("Embarcadero", "Golden Gate Park"): 25,
        ("Embarcadero", "Fisherman's Wharf"): 6,
        ("Embarcadero", "Sunset District"): 30,
        ("Embarcadero", "The Castro"): 25,
        ("Pacific Heights", "Chinatown"): 11,
        ("Pacific Heights", "Embarcadero"): 10,
        ("Pacific Heights", "Russian Hill"): 7,
        ("Pacific Heights", "Haight-Ashbury"): 11,
        ("Pacific Heights", "Golden Gate Park"): 15,
        ("Pacific Heights", "Fisherman's Wharf"): 13,
        ("Pacific Heights", "Sunset District"): 21,
        ("Pacific Heights", "The Castro"): 16,
        ("Russian Hill", "Chinatown"): 9,
        ("Russian Hill", "Embarcadero"): 8,
        ("Russian Hill", "Pacific Heights"): 7,
        ("Russian Hill", "Haight-Ashbury"): 17,
        ("Russian Hill", "Golden Gate Park"): 21,
        ("Russian Hill", "Fisherman's Wharf"): 7,
        ("Russian Hill", "Sunset District"): 23,
        ("Russian Hill", "The Castro"): 21,
        ("Haight-Ashbury", "Chinatown"): 19,
        ("Haight-Ashbury", "Embarcadero"): 20,
        ("Haight-Ashbury", "Pacific Heights"): 12,
        ("Haight-Ashbury", "Russian Hill"): 17,
        ("Haight-Ashbury", "Golden Gate Park"): 7,
        ("Haight-Ashbury", "Fisherman's Wharf"): 23,
        ("Haight-Ashbury", "Sunset District"): 15,
        ("Haight-Ashbury", "The Castro"): 6,
        ("Golden Gate Park", "Chinatown"): 23,
        ("Golden Gate Park", "Embarcadero"): 25,
        ("Golden Gate Park", "Pacific Heights"): 16,
        ("Golden Gate Park", "Russian Hill"): 19,
        ("Golden Gate Park", "Haight-Ashbury"): 7,
        ("Golden Gate Park", "Fisherman's Wharf"): 24,
        ("Golden Gate Park", "Sunset District"): 10,
        ("Golden Gate Park", "The Castro"): 13,
        ("Fisherman's Wharf", "Chinatown"): 12,
        ("Fisherman's Wharf", "Embarcadero"): 8,
        ("Fisherman's Wharf", "Pacific Heights"): 12,
        ("Fisherman's Wharf", "Russian Hill"): 7,
        ("Fisherman's Wharf", "Haight-Ashbury"): 22,
        ("Fisherman's Wharf", "Golden Gate Park"): 25,
        ("Fisherman's Wharf", "Sunset District"): 27,
        ("Fisherman's Wharf", "The Castro"): 27,
        ("Sunset District", "Chinatown"): 30,
        ("Sunset District", "Embarcadero"): 30,
        ("Sunset District", "Pacific Heights"): 21,
        ("Sunset District", "Russian Hill"): 24,
        ("Sunset District", "Haight-Ashbury"): 15,
        ("Sunset District", "Golden Gate Park"): 11,
        ("Sunset District", "Fisherman's Wharf"): 29,
        ("Sunset District", "The Castro"): 17,
        ("The Castro", "Chinatown"): 22,
        ("The Castro", "Embarcadero"): 22,
        ("The Castro", "Pacific Heights"): 16,
        ("The Castro", "Russian Hill"): 18,
        ("The Castro", "Haight-Ashbury"): 6,
        ("The Castro", "Golden Gate Park"): 11,
        ("The Castro", "Fisherman's Wharf"): 24,
        ("The Castro", "Sunset District"): 17
    }

    # Friends data with priority ranking (lower number = higher priority)
    friends = [
        {"name": "Richard", "location": "Embarcadero", "start": (15,15), "end": (18,45), "duration": 90, "priority": 1},
        {"name": "Mark", "location": "Pacific Heights", "start": (15,0), "end": (17,0), "duration": 45, "priority": 3},
        {"name": "Matthew", "location": "Russian Hill", "start": (17,30), "end": (21,0), "duration": 90, "priority": 2},
        {"name": "Rebecca", "location": "Haight-Ashbury", "start": (14,45), "end": (18,0), "duration": 60, "priority": 4},
        {"name": "Melissa", "location": "Golden Gate Park", "start": (13,45), "end": (17,30), "duration": 90, "priority": 5},
        {"name": "Margaret", "location": "Fisherman's Wharf", "start": (14,45), "end": (20,15), "duration": 15, "priority": 8},
        {"name": "Emily", "location": "Sunset District", "start": (15,45), "end": (17,0), "duration": 45, "priority": 7},
        {"name": "George", "location": "The Castro", "start": (14,0), "end": (16,15), "duration": 75, "priority": 6}
    ]

    # Convert time to minutes since 9:00 AM (540 minutes)
    def time_to_minutes(h, m):
        return h * 60 + m - 540

    def minutes_to_time(m):
        total = 540 + m
        h = total // 60
        m = total % 60
        return f"{h:02d}:{m:02d}"

    # Create meeting variables with flexible durations
    meet_vars = []
    for friend in sorted(friends, key=lambda x: x["priority"]):
        start_min = time_to_minutes(*friend["start"])
        end_min = time_to_minutes(*friend["end"])
        start = Int(f"start_{friend['name']}")
        end = Int(f"end_{friend['name']}")
        duration = Int(f"dur_{friend['name']}")
        
        # Flexible duration between minimum and maximum possible
        opt.add(duration >= friend["duration"])
        opt.add(duration <= (end_min - start_min))
        opt.add(start >= start_min)
        opt.add(end <= end_min)
        opt.add(end == start + duration)
        
        meet_vars.append((friend, start, end, duration))

    # Add travel time constraints with ordering
    for i in range(len(meet_vars)):
        for j in range(i+1, len(meet_vars)):
            friend1, start1, end1, _ = meet_vars[i]
            friend2, start2, end2, _ = meet_vars[j]
            
            # Get travel time in both directions
            travel_time1 = travel_times.get((friend1["location"], friend2["location"]), 0)
            travel_time2 = travel_times.get((friend2["location"], friend1["location"]), 0)
            
            # Either meeting1 before meeting2 with travel time, or vice versa
            opt.add(Or(
                start2 >= end1 + travel_time1,
                start1 >= end2 + travel_time2
            ))

    # Maximize both number of meetings and total meeting time
    met = [Bool(f"met_{friend['name']}") for friend in friends]
    total_duration = Int("total_duration")
    opt.add(total_duration == Sum([If(met[i], meet_vars[i][3], 0) for i in range(len(meet_vars))])
    
    for i, (friend, _, _, _) in enumerate(meet_vars):
        opt.add(Implies(met[i], meet_vars[i][3] >= friend["duration"]))
    
    # Prioritize higher priority meetings
    priority_score = Sum([If(met[i], 10 - friends[i]["priority"], 0) for i in range(len(friends))])
    
    # Optimization objectives
    opt.maximize(total_duration)
    opt.maximize(priority_score)
    opt.maximize(Sum([If(m, 1, 0) for m in met]))

    # Solve with a time limit
    opt.set("timeout", 30000)  # 30 second timeout
    
    if opt.check() == sat:
        model = opt.model()
        itinerary = []
        for friend, start, end, _ in meet_vars:
            if model.evaluate(met[friends.index(friend)]):
                start_time = model.evaluate(start).as_long()
                end_time = model.evaluate(end).as_long()
                itinerary.append({
                    "action": "meet",
                    "person": friend["name"],
                    "start_time": minutes_to_time(start_time),
                    "end_time": minutes_to_time(end_time),
                    "location": friend["location"]
                })
        
        # Sort by start time
        itinerary.sort(key=lambda x: x["start_time"])
        
        # Calculate total travel time
        total_travel = 0
        for i in range(len(itinerary)-1):
            from_loc = itinerary[i]["location"]
            to_loc = itinerary[i+1]["location"]
            total_travel += travel_times.get((from_loc, to_loc), 0)
        
        return {
            "itinerary": itinerary,
            "stats": {
                "friends_met": len(itinerary),
                "total_meeting_minutes": sum(
                    (time_to_minutes(int(x["end_time"][:2]), int(x["end_time"][3:5])) - 
                    time_to_minutes(int(x["start_time"][:2]), int(x["start_time"][3:5]))
                    for x in itinerary
                ),
                "total_travel_minutes": total_travel
            }
        }
    else:
        return {"error": "No feasible schedule found with given constraints"}

# Solve and print the solution
solution = solve_scheduling_problem()
print("SOLUTION:")
print(json.dumps(solution, indent=2))