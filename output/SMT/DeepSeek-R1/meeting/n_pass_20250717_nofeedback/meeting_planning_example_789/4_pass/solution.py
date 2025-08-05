from z3 import *

def main():
    travel_times = {
        "Union Square": {
            "Russian Hill": 13,
            "Alamo Square": 15,
            "Haight-Ashbury": 18,
            "Marina District": 18,
            "Bayview": 15,
            "Chinatown": 7,
            "Presidio": 24,
            "Sunset District": 27
        },
        "Russian Hill": {
            "Union Square": 10,
            "Alamo Square": 15,
            "Haight-Ashbury": 17,
            "Marina District": 7,
            "Bayview": 23,
            "Chinatown": 9,
            "Presidio": 14,
            "Sunset District": 23
        },
        "Alamo Square": {
            "Union Square": 14,
            "Russian Hill": 13,
            "Haight-Ashbury": 5,
            "Marina District": 15,
            "Bayview": 16,
            "Chinatown": 15,
            "Presidio": 17,
            "Sunset District": 16
        },
        "Haight-Ashbury": {
            "Union Square": 19,
            "Russian Hill": 17,
            "Alamo Square": 5,
            "Marina District": 17,
            "Bayview": 18,
            "Chinatown": 19,
            "Presidio": 15,
            "Sunset District": 15
        },
        "Marina District": {
            "Union Square": 16,
            "Russian Hill": 8,
            "Alamo Square": 15,
            "Haight-Ashbury": 16,
            "Bayview": 27,
            "Chinatown": 15,
            "Presidio": 10,
            "Sunset District": 19
        },
        "Bayview": {
            "Union Square": 18,
            "Russian Hill": 23,
            "Alamo Square": 16,
            "Haight-Ashbury": 19,
            "Marina District": 27,
            "Chinatown": 19,
            "Presidio": 32,
            "Sunset District": 23
        },
        "Chinatown": {
            "Union Square": 7,
            "Russian Hill": 7,
            "Alamo Square": 17,
            "Haight-Ashbury": 19,
            "Marina District": 12,
            "Bayview": 20,
            "Presidio": 19,
            "Sunset District": 29
        },
        "Presidio": {
            "Union Square": 22,
            "Russian Hill": 14,
            "Alamo Square": 19,
            "Haight-Ashbury": 15,
            "Marina District": 11,
            "Bayview": 31,
            "Chinatown": 21,
            "Sunset District": 15
        },
        "Sunset District": {
            "Union Square": 30,
            "Russian Hill": 24,
            "Alamo Square": 17,
            "Haight-Ashbury": 15,
            "Marina District": 21,
            "Bayview": 22,
            "Chinatown": 30,
            "Presidio": 16
        }
    }

    friends = [
        {"name": "Betty", "location": "Russian Hill", "min_duration": 105, "avail_start": -120, "avail_end": 465},
        {"name": "Melissa", "location": "Alamo Square", "min_duration": 105, "avail_start": 30, "avail_end": 495},
        {"name": "Joshua", "location": "Haight-Ashbury", "min_duration": 90, "avail_start": 195, "avail_end": 600},
        {"name": "Jeffrey", "location": "Marina District", "min_duration": 45, "avail_start": 195, "avail_end": 540},
        {"name": "James", "location": "Bayview", "min_duration": 90, "avail_start": -90, "avail_end": 660},
        {"name": "Anthony", "location": "Chinatown", "min_duration": 75, "avail_start": 165, "avail_end": 270},
        {"name": "Timothy", "location": "Presidio", "min_duration": 90, "avail_start": 210, "avail_end": 345},
        {"name": "Emily", "location": "Sunset District", "min_duration": 120, "avail_start": 630, "avail_end": 750}
    ]

    opt = Optimize()

    meet = [Bool(f"meet_{i}") for i in range(8)]
    start = [Int(f"start_{i}") for i in range(8)]
    end = [Int(f"end_{i}") for i in range(8)]

    opt.add(meet[7] == True)
    opt.add(start[7] == 630)
    opt.add(end[7] == 750)

    for i in range(8):
        opt.add(If(meet[i],
                   And(
                       start[i] >= friends[i]["avail_start"],
                       end[i] == start[i] + friends[i]["min_duration"],
                       end[i] <= friends[i]["avail_end"]
                   ),
                   True))

    for i in range(8):
        loc_i = friends[i]["location"]
        from_union = travel_times["Union Square"][loc_i]
        constraints = [start[i] >= from_union]
        for j in range(8):
            if j == i:
                continue
            loc_j = friends[j]["location"]
            travel_time = travel_times[loc_j][loc_i]
            constraints.append(And(meet[j], end[j] + travel_time <= start[i]))
        opt.add(If(meet[i], Or(constraints), True))

    for i in range(8):
        for j in range(i+1, 8):
            loc_i = friends[i]["location"]
            loc_j = friends[j]["location"]
            time_ij = travel_times[loc_i][loc_j]
            time_ji = travel_times[loc_j][loc_i]
            opt.add(If(And(meet[i], meet[j]),
                     Or(
                         end[i] + time_ij <= start[j],
                         end[j] + time_ji <= start[i]
                     ),
                     True))

    num_meetings = Sum([If(meet[i], 1, 0) for i in range(8)])
    opt.maximize(num_meetings)

    if opt.check() == sat:
        model = opt.model()
        scheduled_meetings = []
        for i in range(8):
            if is_true(model[meet[i]]):
                start_val = model[start[i]].as_long()
                hours = 9 + start_val // 60
                minutes = start_val % 60
                start_str = f"{hours:02d}:{minutes:02d}"

                end_val = model[end[i]].as_long()
                hours = 9 + end_val // 60
                minutes = end_val % 60
                end_str = f"{hours:02d}:{minutes:02d}"

                scheduled_meetings.append({
                    "action": "meet",
                    "person": friends[i]["name"],
                    "start_time": start_str,
                    "end_time": end_str
                })
        scheduled_meetings.sort(key=lambda x: x["start_time"])
        result = {"itinerary": scheduled_meetings}
        print("SOLUTION:")
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()