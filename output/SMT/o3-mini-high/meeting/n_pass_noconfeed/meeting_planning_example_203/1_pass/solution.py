from z3 import Int, Bool, If, Optimize, And, Or, Not, Implies, sat
import json

def format_time(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

def main():
    # Define travel times (in minutes) between locations.
    travel = {
        ("Financial District", "Fisherman's Wharf"): 10,
        ("Financial District", "Pacific Heights"): 13,
        ("Financial District", "Mission District"): 17,
        ("Fisherman's Wharf", "Financial District"): 11,
        ("Fisherman's Wharf", "Pacific Heights"): 12,
        ("Fisherman's Wharf", "Mission District"): 22,
        ("Pacific Heights", "Financial District"): 13,
        ("Pacific Heights", "Fisherman's Wharf"): 13,
        ("Pacific Heights", "Mission District"): 15,
        ("Mission District", "Financial District"): 17,
        ("Mission District", "Fisherman's Wharf"): 22,
        ("Mission District", "Pacific Heights"): 16,
    }

    # The day starts at 9:00AM = 540 minutes after midnight.
    start_time = 540

    # Friend meeting constraints:
    # Each friend is available at a location during a given time window and demands a minimum meeting duration.
    friends = [
        {
            "name": "David",
            "location": "Fisherman's Wharf",
            "avail_start": 645,   # 10:45AM
            "avail_end": 930,     # 15:30 (3:30PM)
            "min_meet": 15
        },
        {
            "name": "Timothy",
            "location": "Pacific Heights",
            "avail_start": 540,   # 9:00AM
            "avail_end": 930,     # 15:30 (3:30PM)
            "min_meet": 75
        },
        {
            "name": "Robert",
            "location": "Mission District",
            "avail_start": 735,   # 12:15PM
            "avail_end": 1185,    # 19:45 (7:45PM)
            "min_meet": 90
        }
    ]

    opt = Optimize()

    # For each friend, create Z3 variables for meeting start time, end time, and a Boolean flag indicating if the meeting is scheduled.
    for f in friends:
        f['s_var'] = Int("s_" + f['name'])
        f['e_var'] = Int("e_" + f['name'])
        f['inc'] = Bool("inc_" + f['name'])
        # Constraint: if meeting is scheduled, then you must travel from the Financial District to their location.
        travel_from_fd = travel[("Financial District", f["location"])]
        opt.add(Implies(f['inc'], f['s_var'] >= start_time + travel_from_fd))
        # The meeting must also fall within the friend’s availability window.
        opt.add(Implies(f['inc'], f['s_var'] >= f['avail_start']))
        opt.add(Implies(f['inc'], f['e_var'] <= f['avail_end']))
        # Enforce the minimum meeting duration.
        opt.add(Implies(f['inc'], f['e_var'] - f['s_var'] >= f['min_meet']))

    # For any two friends that are scheduled, ensure that the meetings do not overlap.
    # Specifically, if meetings for friend i and friend j are both included, then either i's meeting (plus travel time) is finished before j's meeting starts,
    # or vice versa.
    for i in range(len(friends)):
        for j in range(i+1, len(friends)):
            f_i = friends[i]
            f_j = friends[j]
            travel_i_j = travel[(f_i["location"], f_j["location"])]
            travel_j_i = travel[(f_j["location"], f_i["location"])]
            opt.add(
                Implies(
                    And(f_i['inc'], f_j['inc']),
                    Or(f_i['e_var'] + travel_i_j <= f_j['s_var'],
                       f_j['e_var'] + travel_j_i <= f_i['s_var'])
                )
            )

    # Optimization objective: maximize the number of meetings scheduled.
    total_meetings = sum([If(f['inc'], 1, 0) for f in friends])
    opt.maximize(total_meetings)

    if opt.check() == sat:
        model = opt.model()
        scheduled = []
        for f in friends:
            if model.evaluate(f['inc']):
                s_val = model.evaluate(f['s_var']).as_long()
                e_val = model.evaluate(f['e_var']).as_long()
                scheduled.append({
                    "person": f["name"],
                    "location": f["location"],
                    "start": s_val,
                    "end": e_val
                })
        # Sort the meetings in chronological order based on start_time.
        scheduled.sort(key=lambda x: x["start"])
        itinerary = []
        for meeting in scheduled:
            itinerary.append({
                "action": "meet",
                "location": meeting["location"],
                "person": meeting["person"],
                "start_time": format_time(meeting["start"]),
                "end_time": format_time(meeting["end"])
            })
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()