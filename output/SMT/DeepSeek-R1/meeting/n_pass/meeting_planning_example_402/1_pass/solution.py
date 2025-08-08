from z3 import *

def main():
    travel_times = {
        "Golden Gate Park": {"Haight-Ashbury": 7, "Sunset District": 10, "Marina District": 16, "Financial District": 26, "Union Square": 22},
        "Haight-Ashbury": {"Golden Gate Park": 7, "Sunset District": 15, "Marina District": 17, "Financial District": 21, "Union Square": 17},
        "Sunset District": {"Golden Gate Park": 11, "Haight-Ashbury": 15, "Marina District": 21, "Financial District": 30, "Union Square": 30},
        "Marina District": {"Golden Gate Park": 18, "Haight-Ashbury": 16, "Sunset District": 19, "Financial District": 17, "Union Square": 16},
        "Financial District": {"Golden Gate Park": 23, "Haight-Ashbury": 19, "Sunset District": 31, "Marina District": 15, "Union Square": 9},
        "Union Square": {"Golden Gate Park": 22, "Haight-Ashbury": 18, "Sunset District": 26, "Marina District": 18, "Financial District": 9}
    }

    friends = [
        {"name": "Matthew", "loc": "Marina District", "start_avail": 15, "end_avail": 180, "min_dur": 15},
        {"name": "Robert", "loc": "Union Square", "start_avail": 75, "end_avail": 765, "min_dur": 15},
        {"name": "Joseph", "loc": "Financial District", "start_avail": 315, "end_avail": 585, "min_dur": 30},
        {"name": "Patricia", "loc": "Sunset District", "start_avail": 480, "end_avail": 645, "min_dur": 45},
        {"name": "Sarah", "loc": "Haight-Ashbury", "start_avail": 480, "end_avail": 750, "min_dur": 105}
    ]

    s = Optimize()
    n_friends = len(friends)
    meet = [Bool(f"meet_{i}") for i in range(n_friends)]
    start = [Int(f"start_{i}") for i in range(n_friends)]
    end = [Int(f"end_{i}") for i in range(n_friends)]
    order = [Int(f"order_{i}") for i in range(n_friends)]

    total_meetings = Int('total_meetings')
    s.add(total_meetings == Sum([If(meet[i], 1, 0) for i in range(n_friends)]))

    for i in range(n_friends):
        s.add(If(meet[i],
                 And(start[i] >= friends[i]["start_avail"],
                     end[i] <= friends[i]["end_avail"],
                     end[i] == start[i] + friends[i]["min_dur"]),
                 True))
        s.add(meet[i] == (order[i] > 0))
        s.add(If(meet[i], And(order[i] >= 1, order[i] <= n_friends), order[i] == 0))

    for i in range(n_friends):
        for j in range(i + 1, n_friends):
            s.add(If(And(meet[i], meet[j]), order[i] != order[j], True))

    for j in range(n_friends):
        first_meet_condition = And(
            meet[j],
            order[j] == 1,
            start[j] >= travel_times["Golden Gate Park"][friends[j]["loc"]]
        )
        other_conditions = []
        for i in range(n_friends):
            if i == j:
                continue
            cond = And(
                meet[i],
                meet[j],
                order[i] == order[j] - 1,
                start[j] >= end[i] + travel_times[friends[i]["loc"]][friends[j]["loc"]]
            )
            other_conditions.append(cond)
        condition = Or(first_meet_condition, Or(other_conditions))
        s.add(If(meet[j], condition, True))

    s.maximize(total_meetings)

    if s.check() == sat:
        m = s.model()
        scheduled_meetings = []
        for i in range(n_friends):
            if m.evaluate(meet[i]):
                start_val = m.evaluate(start[i]).as_long()
                end_val = m.evaluate(end[i]).as_long()
                base_hour = 9
                hour = base_hour + start_val // 60
                minute = start_val % 60
                start_time_str = f"{hour:02d}:{minute:02d}"
                hour_end = base_hour + end_val // 60
                minute_end = end_val % 60
                end_time_str = f"{hour_end:02d}:{minute_end:02d}"
                scheduled_meetings.append({
                    "action": "meet",
                    "person": friends[i]["name"],
                    "start_time": start_time_str,
                    "end_time": end_time_str
                })
        scheduled_meetings.sort(key=lambda x: x['start_time'])
        result = {"itinerary": scheduled_meetings}
        print(f"SOLUTION: {result}")
    else:
        print("SOLUTION: {\"itinerary\": []}")

if __name__ == "__main__":
    main()