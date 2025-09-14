import json
from z3 import Optimize, Int, Bool, And, Or, Implies, If, Sum, Not

def minutes_to_str(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

def main():
    # Locations
    locations = [
        "Presidio",
        "Richmond District",
        "North Beach",
        "Financial District",
        "Golden Gate Park",
        "Union Square",
    ]

    # Travel times in minutes (asymmetric, as provided)
    travel = {
        ("Presidio", "Richmond District"): 7,
        ("Presidio", "North Beach"): 18,
        ("Presidio", "Financial District"): 23,
        ("Presidio", "Golden Gate Park"): 12,
        ("Presidio", "Union Square"): 22,
        ("Richmond District", "Presidio"): 7,
        ("Richmond District", "North Beach"): 17,
        ("Richmond District", "Financial District"): 22,
        ("Richmond District", "Golden Gate Park"): 9,
        ("Richmond District", "Union Square"): 21,
        ("North Beach", "Presidio"): 17,
        ("North Beach", "Richmond District"): 18,
        ("North Beach", "Financial District"): 8,
        ("North Beach", "Golden Gate Park"): 22,
        ("North Beach", "Union Square"): 7,
        ("Financial District", "Presidio"): 22,
        ("Financial District", "Richmond District"): 21,
        ("Financial District", "North Beach"): 7,
        ("Financial District", "Golden Gate Park"): 23,
        ("Financial District", "Union Square"): 9,
        ("Golden Gate Park", "Presidio"): 11,
        ("Golden Gate Park", "Richmond District"): 7,
        ("Golden Gate Park", "North Beach"): 24,
        ("Golden Gate Park", "Financial District"): 26,
        ("Golden Gate Park", "Union Square"): 22,
        ("Union Square", "Presidio"): 24,
        ("Union Square", "Richmond District"): 20,
        ("Union Square", "North Beach"): 10,
        ("Union Square", "Financial District"): 9,
        ("Union Square", "Golden Gate Park"): 22,
    }

    def get_travel(a, b):
        return travel[(a, b)]

    # Arrival at Presidio 9:00 -> 540 minutes
    arrival_location = "Presidio"
    arrival_time = 540

    # People constraints: availability windows and minimum meeting duration (minutes)
    # Times are in minutes from midnight, 24-hour format
    persons = [
        {
            "name": "Jason",
            "location": "Richmond District",
            "avail_start": 13 * 60,       # 13:00
            "avail_end": 20 * 60 + 45,    # 20:45
            "min_duration": 90,
        },
        {
            "name": "Melissa",
            "location": "North Beach",
            "avail_start": 18 * 60 + 45,  # 18:45
            "avail_end": 20 * 60 + 15,    # 20:15
            "min_duration": 45,
        },
        {
            "name": "Brian",
            "location": "Financial District",
            "avail_start": 9 * 60 + 45,   # 9:45
            "avail_end": 21 * 60 + 45,    # 21:45
            "min_duration": 15,
        },
        {
            "name": "Elizabeth",
            "location": "Golden Gate Park",
            "avail_start": 8 * 60 + 45,   # 8:45
            "avail_end": 21 * 60 + 30,    # 21:30
            "min_duration": 105,
        },
        {
            "name": "Laura",
            "location": "Union Square",
            "avail_start": 14 * 60 + 15,  # 14:15
            "avail_end": 19 * 60 + 30,    # 19:30
            "min_duration": 75,
        },
    ]

    # Z3 variables
    opt = Optimize()
    opt.set(priority='lex')

    meet = {}
    start = {}
    dur = {}
    end = {}

    # Bounds for times
    DAY_START = 0
    DAY_END = 24 * 60  # 1440

    for p in persons:
        name = p["name"]
        meet[name] = Bool(f"meet_{name}")
        start[name] = Int(f"start_{name}")
        dur[name] = Int(f"dur_{name}")
        end[name] = Int(f"end_{name}")

        # Basic bounds
        opt.add(start[name] >= DAY_START, start[name] <= DAY_END)
        opt.add(dur[name] >= 0)
        opt.add(end[name] == start[name] + dur[name])

        # If meeting, enforce within availability and min duration
        opt.add(Implies(
            meet[name],
            And(
                start[name] >= p["avail_start"],
                end[name] <= p["avail_end"],
                dur[name] >= p["min_duration"]
            )
        ))

        # If not meeting, zero duration (end == start ensured above)
        opt.add(Implies(
            Not(meet[name]),
            And(dur[name] == 0)
        ))

        # Reachability from arrival at Presidio before the meeting starts
        # Any meeting must start after we could have traveled from Presidio at arrival time
        # (This is safe given all travel times are short)
        opt.add(Implies(
            meet[name],
            start[name] >= arrival_time + get_travel(arrival_location, p["location"])
        ))

    # Non-overlap and travel time constraints between all pairs of meetings
    for i in range(len(persons)):
        for j in range(i + 1, len(persons)):
            pi = persons[i]
            pj = persons[j]
            ni = pi["name"]
            nj = pj["name"]
            li = pi["location"]
            lj = pj["location"]

            # If both meetings occur, they must be ordered with enough travel time in between
            opt.add(Implies(
                And(meet[ni], meet[nj]),
                Or(
                    end[ni] + get_travel(li, lj) <= start[nj],
                    end[nj] + get_travel(lj, li) <= start[ni]
                )
            ))

    # Objectives: maximize number of meetings, then maximize total meeting time
    count_meetings = Sum([If(meet[p["name"]], 1, 0) for p in persons])
    total_meeting_time = Sum([dur[p["name"]] for p in persons])

    opt.maximize(count_meetings)
    opt.maximize(total_meeting_time)

    result = opt.check()
    itinerary = []

    if str(result) == 'sat':
        model = opt.model()
        meetings = []
        for p in persons:
            name = p["name"]
            if model.evaluate(meet[name], model_completion=True):
                s = model.evaluate(start[name], model_completion=True).as_long()
                e = model.evaluate(end[name], model_completion=True).as_long()
                meetings.append({
                    "action": "meet",
                    "location": p["location"],
                    "person": name,
                    "start_time": minutes_to_str(s),
                    "end_time": minutes_to_str(e),
                    "start_minutes": s  # for sorting
                })
        # Sort by start time
        meetings.sort(key=lambda x: x["start_minutes"])
        # Remove helper field
        for m in meetings:
            m.pop("start_minutes", None)
        itinerary = meetings
    else:
        itinerary = []

    output = {"itinerary": itinerary}
    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()