from z3 import Optimize, Int, Bool, If, And, Or, Implies, Not, Sum
import json

def format_time(t):
    # t is in minutes from midnight, return string in H:MM 24-hour format
    hours = t // 60
    minutes = t % 60
    return f"{hours}:{minutes:02d}"

def main():
    # Define meeting data for each friend
    # Times are in minutes from midnight.
    # 8:00 = 480, 9:00 = 540, 10:00 = 600, 13:30 = 810, 18:00 = 1080, 21:30 = 1290, 22:00 = 1320.
    meetings = [
        { "person": "Jeffrey", "location": "Presidio",           "avail_start": 480,  "avail_end": 600,  "min_duration": 105 },
        { "person": "Steven",  "location": "North Beach",        "avail_start": 810,  "avail_end": 1320, "min_duration": 45  },
        { "person": "Barbara", "location": "Fisherman's Wharf",  "avail_start": 1080, "avail_end": 1290, "min_duration": 30  },
        { "person": "John",    "location": "Pacific Heights",    "avail_start": 540,  "avail_end": 810,  "min_duration": 15  }
    ]
    N = len(meetings)
    
    # Define travel times as given (in minutes)
    travel = {
        ("Nob Hill", "Presidio"): 17,
        ("Nob Hill", "North Beach"): 8,
        ("Nob Hill", "Fisherman's Wharf"): 11,
        ("Nob Hill", "Pacific Heights"): 8,
        ("Presidio", "Nob Hill"): 18,
        ("Presidio", "North Beach"): 18,
        ("Presidio", "Fisherman's Wharf"): 19,
        ("Presidio", "Pacific Heights"): 11,
        ("North Beach", "Nob Hill"): 7,
        ("North Beach", "Presidio"): 17,
        ("North Beach", "Fisherman's Wharf"): 5,
        ("North Beach", "Pacific Heights"): 8,
        ("Fisherman's Wharf", "Nob Hill"): 11,
        ("Fisherman's Wharf", "Presidio"): 17,
        ("Fisherman's Wharf", "North Beach"): 6,
        ("Fisherman's Wharf", "Pacific Heights"): 12,
        ("Pacific Heights", "Nob Hill"): 8,
        ("Pacific Heights", "Presidio"): 11,
        ("Pacific Heights", "North Beach"): 9,
        ("Pacific Heights", "Fisherman's Wharf"): 13,
    }
    
    # Arrival time: You arrive at Nob Hill at 9:00 (540)
    arrival_time = 540

    opt = Optimize()

    # Decision variables for each meeting
    x = [Bool(f"x{i}") for i in range(N)]         # Whether meeting i is scheduled
    start = [Int(f"start{i}") for i in range(N)]    # Meeting start time
    end = [Int(f"end{i}") for i in range(N)]        # Meeting end time
    order = [Int(f"order{i}") for i in range(N)]    # Order in which meeting i is visited; if unscheduled, set to -1

    for i in range(N):
        m = meetings[i]
        # If meeting i is scheduled then:
        # - Meeting must start no earlier than the friend’s available start.
        # - Meeting must finish no later than the friend’s available end.
        # - Meeting must be at least the minimum duration.
        opt.add(Implies(x[i], start[i] >= m["avail_start"]))
        opt.add(Implies(x[i], end[i] <= m["avail_end"]))
        opt.add(Implies(x[i], end[i] - start[i] >= m["min_duration"]))
        opt.add(Implies(x[i], start[i] < end[i]))
        # Ordering variables: If scheduled, order is between 0 and N-1; if not, it is -1.
        opt.add(Implies(x[i], And(order[i] >= 0, order[i] < N)))
        opt.add(Implies(Not(x[i]), order[i] == -1))
        # For meetings that are chosen as the first meeting (order == 0),
        # account for travel time from Nob Hill.
        opt.add(Implies(And(x[i], order[i] == 0),
                        start[i] >= arrival_time + travel[("Nob Hill", m["location"])]))
    
    # Enforce that if two meetings are scheduled, their order variables must be distinct.
    for i in range(N):
        for j in range(i+1, N):
            opt.add(Implies(And(x[i], x[j]), order[i] != order[j]))
    
    # Enforce consecutive ordering: For any meeting with order > 0, there must exist a meeting with order one less.
    for i in range(N):
        # Only add if meeting i is scheduled and its order is > 0.
        opt.add(Implies(And(x[i], order[i] > 0),
                        Or([And(x[j], order[j] == order[i] - 1) for j in range(N) if j != i] or [False])))
    
    # Enforce travel time constraints between consecutive meetings.
    # For any two meetings i and j, if both are scheduled and j is immediately after i (i.e. order[j] == order[i] + 1),
    # then meeting j must start after meeting i ends plus travel time from meeting i's location to meeting j's location.
    for i in range(N):
        for j in range(N):
            if i != j:
                loc_i = meetings[i]["location"]
                loc_j = meetings[j]["location"]
                # Only add if the key exists in travel dictionary.
                if (loc_i, loc_j) in travel:
                    opt.add(Implies(And(x[i], x[j], order[j] == order[i] + 1),
                                    start[j] >= end[i] + travel[(loc_i, loc_j)]))
    
    # Objective: maximize the number of meetings scheduled.
    obj = opt.maximize(Sum([If(x[i], 1, 0) for i in range(N)]))
    
    if opt.check() == 'sat' or opt.check() is not None:
        model = opt.model()
        
        # Collect scheduled meetings and sort them by their order value.
        scheduled = []
        for i in range(N):
            if model.evaluate(x[i]):
                s = model.evaluate(start[i]).as_long()
                e = model.evaluate(end[i]).as_long()
                o = model.evaluate(order[i]).as_long()
                scheduled.append((o, {
                    "action": "meet",
                    "location": meetings[i]["location"],
                    "person": meetings[i]["person"],
                    "start_time": format_time(s),
                    "end_time": format_time(e)
                }))
        scheduled.sort(key=lambda x: x[0])
        itinerary = [item[1] for item in scheduled]
        output = {"itinerary": itinerary}
        print(json.dumps(output, indent=2))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()