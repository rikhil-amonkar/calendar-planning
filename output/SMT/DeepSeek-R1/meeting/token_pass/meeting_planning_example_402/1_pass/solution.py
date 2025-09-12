from z3 import *
import json

def main():
    # Convert time string to minutes since 9:00 AM
    def time_to_minutes(t):
        hours, minutes = map(int, t.split(':'))
        return (hours - 9) * 60 + minutes

    # Convert minutes since 9:00 AM to time string
    def minutes_to_time(m):
        total_minutes = 9 * 60 + m
        hours = total_minutes // 60
        minutes = total_minutes % 60
        return f"{hours}:{minutes:02d}"

    # Travel time dictionary
    travel_times = {
        ("Golden Gate Park", "Haight-Ashbury"): 7,
        ("Golden Gate Park", "Sunset District"): 10,
        ("Golden Gate Park", "Marina District"): 16,
        ("Golden Gate Park", "Financial District"): 26,
        ("Golden Gate Park", "Union Square"): 22,
        ("Haight-Ashbury", "Golden Gate Park"): 7,
        ("Haight-Ashbury", "Sunset District"): 15,
        ("Haight-Ashbury", "Marina District"): 17,
        ("Haight-Ashbury", "Financial District"): 21,
        ("Haight-Ashbury", "Union Square"): 17,
        ("Sunset District", "Golden Gate Park"): 11,
        ("Sunset District", "Haight-Ashbury"): 15,
        ("Sunset District", "Marina District"): 21,
        ("Sunset District", "Financial District"): 30,
        ("Sunset District", "Union Square"): 30,
        ("Marina District", "Golden Gate Park"): 18,
        ("Marina District", "Haight-Ashbury"): 16,
        ("Marina District", "Sunset District"): 19,
        ("Marina District", "Financial District"): 17,
        ("Marina District", "Union Square"): 16,
        ("Financial District", "Golden Gate Park"): 23,
        ("Financial District", "Haight-Ashbury"): 19,
        ("Financial District", "Sunset District"): 31,
        ("Financial District", "Marina District"): 15,
        ("Financial District", "Union Square"): 9,
        ("Union Square", "Golden Gate Park"): 22,
        ("Union Square", "Haight-Ashbury"): 18,
        ("Union Square", "Sunset District"): 26,
        ("Union Square", "Marina District"): 18,
        ("Union Square", "Financial District"): 9
    }

    # Meeting constraints
    meetings = [
        {
            "person": "Sarah",
            "location": "Haight-Ashbury",
            "avail_start": time_to_minutes("17:00"),
            "avail_end": time_to_minutes("21:30"),
            "min_duration": 105
        },
        {
            "person": "Patricia",
            "location": "Sunset District",
            "avail_start": time_to_minutes("17:00"),
            "avail_end": time_to_minutes("19:45"),
            "min_duration": 45
        },
        {
            "person": "Matthew",
            "location": "Marina District",
            "avail_start": time_to_minutes("9:15"),
            "avail_end": time_to_minutes("12:00"),
            "min_duration": 15
        },
        {
            "person": "Joseph",
            "location": "Financial District",
            "avail_start": time_to_minutes("14:15"),
            "avail_end": time_to_minutes("18:45"),
            "min_duration": 30
        },
        {
            "person": "Robert",
            "location": "Union Square",
            "avail_start": time_to_minutes("10:15"),
            "avail_end": time_to_minutes("21:45"),
            "min_duration": 15
        }
    ]

    n = len(meetings)
    solver = Optimize()

    # Decision variables
    meet_flags = [Bool(f"meet_{i}") for i in range(n)]
    start_times = [Int(f"start_{i}") for i in range(n)]
    end_times = [Int(f"end_{i}") for i in range(n)]
    order = [Int(f"order_{i}") for i in range(n)]
    prev_location = [String(f"prev_loc_{i}") for i in range(n)]

    # Initial location and time
    current_time = 0
    current_location = "Golden Gate Park"

    # Constraints for each meeting
    for i in range(n):
        m = meetings[i]
        # If meeting occurs, constraints on time and duration
        solver.add(Implies(meet_flags[i], And(
            start_times[i] >= m["avail_start"],
            end_times[i] <= m["avail_end"],
            end_times[i] - start_times[i] >= m["min_duration"],
            start_times[i] >= 0
        )))
        # If not meeting, set times to 0
        solver.add(Implies(Not(meet_flags[i]), And(start_times[i] == 0, end_times[i] == 0)))

    # Order constraints: each meeting has a unique order if selected
    solver.add(Distinct([If(meet_flags[i], order[i], -1) for i in range(n)]))
    for i in range(n):
        solver.add(If(meet_flags[i], And(order[i] >= 0, order[i] < n), order[i] == -1))

    # Travel time constraints between consecutive meetings
    for i in range(n):
        for j in range(n):
            if i != j:
                # If both meetings occur and i comes immediately before j
                travel_key = (meetings[i]["location"], meetings[j]["location"])
                travel_time = travel_times.get(travel_key, 0)
                solver.add(Implies(And(meet_flags[i], meet_flags[j], order[j] == order[i] + 1),
                                 start_times[j] >= end_times[i] + travel_time))

    # Travel time from start location to first meeting
    for i in range(n):
        travel_key = (current_location, meetings[i]["location"])
        travel_time = travel_times.get(travel_key, 0)
        solver.add(Implies(And(meet_flags[i], order[i] == 0), start_times[i] >= current_time + travel_time))

    # Maximize number of meetings
    solver.maximize(Sum([If(meet_flags[i], 1, 0) for i in range(n)]))

    # Check feasibility
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        meeting_list = []
        for i in range(n):
            if is_true(model.eval(meet_flags[i])):
                start_val = model.eval(start_times[i]).as_long()
                end_val = model.eval(end_times[i]).as_long()
                meeting_list.append({
                    "index": i,
                    "start": start_val,
                    "end": end_val,
                    "person": meetings[i]["person"],
                    "location": meetings[i]["location"]
                })
        # Sort by start time
        meeting_list.sort(key=lambda x: x["start"])
        for meet in meeting_list:
            itinerary.append({
                "action": "meet",
                "location": meet["location"],
                "person": meet["person"],
                "start_time": minutes_to_time(meet["start"]),
                "end_time": minutes_to_time(meet["end"])
            })
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()