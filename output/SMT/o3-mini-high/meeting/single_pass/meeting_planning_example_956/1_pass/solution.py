from z3 import *
import json

def solve_schedule():
    # Define friend data with location, availability window (in minutes after midnight)
    # and minimum meeting duration (in minutes).
    # Times: 9:00 = 540, e.g. William: [15:15,17:15] becomes [915,1035]
    friends = {
        "William": {"location": "Alamo Square", "window": (915, 1035), "duration": 60},
        "Joshua": {"location": "Richmond District", "window": (420, 1200), "duration": 15},
        "Joseph": {"location": "Financial District", "window": (675, 810), "duration": 15},
        "David": {"location": "Union Square", "window": (1005, 1155), "duration": 45},
        "Brian": {"location": "Fisherman's Wharf", "window": (825, 1245), "duration": 105},
        "Karen": {"location": "Marina District", "window": (690, 1110), "duration": 15},
        "Anthony": {"location": "Haight-Ashbury", "window": (435, 630), "duration": 30},
        "Matthew": {"location": "Mission District", "window": (1035, 1155), "duration": 120},
        "Helen": {"location": "Pacific Heights", "window": (480, 720), "duration": 75},
        "Jeffrey": {"location": "Golden Gate Park", "window": (1140, 1290), "duration": 60}
    }

    # Travel time (in minutes) between locations. Note that some travel times are not symmetric.
    travel_times = {
        ("The Castro", "Alamo Square"): 8,
        ("The Castro", "Richmond District"): 16,
        ("The Castro", "Financial District"): 21,
        ("The Castro", "Union Square"): 19,
        ("The Castro", "Fisherman's Wharf"): 24,
        ("The Castro", "Marina District"): 21,
        ("The Castro", "Haight-Ashbury"): 6,
        ("The Castro", "Mission District"): 7,
        ("The Castro", "Pacific Heights"): 16,
        ("The Castro", "Golden Gate Park"): 11,

        ("Alamo Square", "The Castro"): 8,
        ("Alamo Square", "Richmond District"): 11,
        ("Alamo Square", "Financial District"): 17,
        ("Alamo Square", "Union Square"): 14,
        ("Alamo Square", "Fisherman's Wharf"): 19,
        ("Alamo Square", "Marina District"): 15,
        ("Alamo Square", "Haight-Ashbury"): 5,
        ("Alamo Square", "Mission District"): 10,
        ("Alamo Square", "Pacific Heights"): 10,
        ("Alamo Square", "Golden Gate Park"): 9,

        ("Richmond District", "The Castro"): 16,
        ("Richmond District", "Alamo Square"): 13,
        ("Richmond District", "Financial District"): 22,
        ("Richmond District", "Union Square"): 21,
        ("Richmond District", "Fisherman's Wharf"): 18,
        ("Richmond District", "Marina District"): 9,
        ("Richmond District", "Haight-Ashbury"): 10,
        ("Richmond District", "Mission District"): 20,
        ("Richmond District", "Pacific Heights"): 10,
        ("Richmond District", "Golden Gate Park"): 9,

        ("Financial District", "The Castro"): 20,
        ("Financial District", "Alamo Square"): 17,
        ("Financial District", "Richmond District"): 21,
        ("Financial District", "Union Square"): 9,
        ("Financial District", "Fisherman's Wharf"): 10,
        ("Financial District", "Marina District"): 15,
        ("Financial District", "Haight-Ashbury"): 19,
        ("Financial District", "Mission District"): 17,
        ("Financial District", "Pacific Heights"): 13,
        ("Financial District", "Golden Gate Park"): 23,

        ("Union Square", "The Castro"): 17,
        ("Union Square", "Alamo Square"): 15,
        ("Union Square", "Richmond District"): 20,
        ("Union Square", "Financial District"): 9,
        ("Union Square", "Fisherman's Wharf"): 15,
        ("Union Square", "Marina District"): 18,
        ("Union Square", "Haight-Ashbury"): 18,
        ("Union Square", "Mission District"): 14,
        ("Union Square", "Pacific Heights"): 15,
        ("Union Square", "Golden Gate Park"): 22,

        ("Fisherman's Wharf", "The Castro"): 27,
        ("Fisherman's Wharf", "Alamo Square"): 21,
        ("Fisherman's Wharf", "Richmond District"): 18,
        ("Fisherman's Wharf", "Financial District"): 11,
        ("Fisherman's Wharf", "Union Square"): 13,
        ("Fisherman's Wharf", "Marina District"): 9,
        ("Fisherman's Wharf", "Haight-Ashbury"): 22,
        ("Fisherman's Wharf", "Mission District"): 22,
        ("Fisherman's Wharf", "Pacific Heights"): 12,
        ("Fisherman's Wharf", "Golden Gate Park"): 25,

        ("Marina District", "The Castro"): 22,
        ("Marina District", "Alamo Square"): 15,
        ("Marina District", "Richmond District"): 11,
        ("Marina District", "Financial District"): 17,
        ("Marina District", "Union Square"): 16,
        ("Marina District", "Fisherman's Wharf"): 9,  # assumed symmetric to the reverse
        ("Marina District", "Haight-Ashbury"): 16,
        ("Marina District", "Mission District"): 20,
        ("Marina District", "Pacific Heights"): 7,
        ("Marina District", "Golden Gate Park"): 18,

        ("Haight-Ashbury", "The Castro"): 6,
        ("Haight-Ashbury", "Alamo Square"): 5,
        ("Haight-Ashbury", "Richmond District"): 10,
        ("Haight-Ashbury", "Financial District"): 21,
        ("Haight-Ashbury", "Union Square"): 19,
        ("Haight-Ashbury", "Fisherman's Wharf"): 23,
        ("Haight-Ashbury", "Marina District"): 17,
        ("Haight-Ashbury", "Mission District"): 11,
        ("Haight-Ashbury", "Pacific Heights"): 12,
        ("Haight-Ashbury", "Golden Gate Park"): 7,

        ("Mission District", "The Castro"): 7,
        ("Mission District", "Alamo Square"): 11,
        ("Mission District", "Richmond District"): 20,
        ("Mission District", "Financial District"): 15,
        ("Mission District", "Union Square"): 15,
        ("Mission District", "Fisherman's Wharf"): 22,
        ("Mission District", "Marina District"): 19,
        ("Mission District", "Haight-Ashbury"): 12,
        ("Mission District", "Pacific Heights"): 16,
        ("Mission District", "Golden Gate Park"): 17,

        ("Pacific Heights", "The Castro"): 16,
        ("Pacific Heights", "Alamo Square"): 10,
        ("Pacific Heights", "Richmond District"): 12,
        ("Pacific Heights", "Financial District"): 13,
        ("Pacific Heights", "Union Square"): 12,
        ("Pacific Heights", "Fisherman's Wharf"): 13,
        ("Pacific Heights", "Marina District"): 7,
        ("Pacific Heights", "Haight-Ashbury"): 11,
        ("Pacific Heights", "Mission District"): 15,
        ("Pacific Heights", "Golden Gate Park"): 15,

        ("Golden Gate Park", "The Castro"): 13,
        ("Golden Gate Park", "Alamo Square"): 9,
        ("Golden Gate Park", "Richmond District"): 7,
        ("Golden Gate Park", "Financial District"): 26,
        ("Golden Gate Park", "Union Square"): 22,
        ("Golden Gate Park", "Fisherman's Wharf"): 24,
        ("Golden Gate Park", "Marina District"): 16,
        ("Golden Gate Park", "Haight-Ashbury"): 7,
        ("Golden Gate Park", "Mission District"): 17,
        ("Golden Gate Park", "Pacific Heights"): 16,
    }
    
    # We arrive at "The Castro" at 9:00 AM (i.e. 540 minutes)
    start_castro = 540
    
    # Create an Optimize solver because we want to maximize the number of meetings.
    opt = Optimize()
    
    # Create Z3 variables for each friend:
    #   sch[f]: Boolean indicator whether we decide to meet friend f.
    #   start_vars[f] and end_vars[f]: integer meeting start and end times (in minutes)
    sch = {}
    start_vars = {}
    end_vars = {}
    
    for f in friends:
        sch[f] = Bool("sch_" + f)
        start_vars[f] = Int("start_" + f)
        end_vars[f] = Int("end_" + f)
        avail_start, avail_end = friends[f]["window"]
        duration = friends[f]["duration"]
        loc = friends[f]["location"]
        # If the meeting is taken then its start time must be no earlier than:
        # a) the friend’s available window start, and
        # b) our arrival time at that location coming from The Castro.
        opt.add(Implies(sch[f], start_vars[f] >= avail_start))
        opt.add(Implies(sch[f], start_vars[f] >= start_castro + travel_times[("The Castro", loc)]))
        # The meeting must finish by the friend’s window end.
        opt.add(Implies(sch[f], end_vars[f] <= avail_end))
        # The meeting must last at least the required duration.
        opt.add(Implies(sch[f], end_vars[f] - start_vars[f] >= duration))
    
    # For any two meetings that we choose, enforce non-overlap using travel times.
    # That is, for any two distinct friends f and g, if both meetings are scheduled then:
    # either the meeting f (plus travel from f to g) finishes before g starts,
    # or the meeting g (plus travel from g to f) finishes before f starts.
    friend_list = list(friends.keys())
    n = len(friend_list)
    for i in range(n):
        for j in range(i + 1, n):
            f1 = friend_list[i]
            f2 = friend_list[j]
            loc1 = friends[f1]["location"]
            loc2 = friends[f2]["location"]
            c = Implies(And(sch[f1], sch[f2]),
                        Or(end_vars[f1] + travel_times[(loc1, loc2)] <= start_vars[f2],
                           end_vars[f2] + travel_times[(loc2, loc1)] <= start_vars[f1]))
            opt.add(c)
    
    # Our objective is to maximize the number of meetings scheduled.
    total_meetings = Sum([If(sch[f], 1, 0) for f in friend_list])
    opt.maximize(total_meetings)
    
    # Check for a solution.
    if opt.check() == sat:
        model = opt.model()
        # Build the itinerary from scheduled meetings, sorting them by start time.
        scheduled_meetings = []
        for f in friend_list:
            if is_true(model.evaluate(sch[f])):
                st = model.evaluate(start_vars[f]).as_long()
                et = model.evaluate(end_vars[f]).as_long()
                scheduled_meetings.append((st, et, f))
        scheduled_meetings.sort(key=lambda x: x[0])
        
        # Helper: convert minutes to an HH:MM string.
        def format_time(t):
            h = t // 60
            m = t % 60
            return f"{h:02d}:{m:02d}"
        
        itinerary = []
        for (st, et, f) in scheduled_meetings:
            itinerary.append({
                "action": "meet",
                "person": f,
                "start_time": format_time(st),
                "end_time": format_time(et)
            })
        
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found.")

if __name__ == "__main__":
    solve_schedule()