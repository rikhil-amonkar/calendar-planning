from z3 import *
import json

def main():
    friends = ['Rebecca', 'Linda', 'Elizabeth', 'William', 'Robert', 'Mark']
    locations = {
        'Rebecca': 'Presidio',
        'Linda': 'Sunset District',
        'Elizabeth': 'Haight-Ashbury',
        'William': 'Mission District',
        'Robert': 'Golden Gate Park',
        'Mark': 'Russian Hill'
    }
    min_durations = {
        'Rebecca': 60,
        'Linda': 30,
        'Elizabeth': 105,
        'William': 30,
        'Robert': 45,
        'Mark': 75
    }
    available_start = {
        'Rebecca': 1095,   # 6:15 PM (18*60+15)
        'Linda': 930,       # 3:30 PM (15*60+30)
        'Elizabeth': 1035,  # 5:15 PM (17*60+15)
        'William': 795,     # 1:15 PM (13*60+15)
        'Robert': 855,      # 2:15 PM (14*60+15)
        'Mark': 600         # 10:00 AM (10*60)
    }
    available_end = {
        'Rebecca': 1245,    # 8:45 PM (20*60+45)
        'Linda': 1185,      # 7:45 PM (19*60+45)
        'Elizabeth': 1170,  # 7:30 PM (19*60+30)
        'William': 1170,    # 7:30 PM (19*60+30)
        'Robert': 1290,     # 9:30 PM (21*60+30)
        'Mark': 1275        # 9:15 PM (21*60+15)
    }

    travel_time_dict = {
        'The Castro': {
            'Presidio': 20,
            'Sunset District': 17,
            'Haight-Ashbury': 6,
            'Mission District': 7,
            'Golden Gate Park': 11,
            'Russian Hill': 18
        },
        'Presidio': {
            'The Castro': 21,
            'Sunset District': 15,
            'Haight-Ashbury': 15,
            'Mission District': 26,
            'Golden Gate Park': 12,
            'Russian Hill': 14
        },
        'Sunset District': {
            'The Castro': 17,
            'Presidio': 16,
            'Haight-Ashbury': 15,
            'Mission District': 24,
            'Golden Gate Park': 11,
            'Russian Hill': 24
        },
        'Haight-Ashbury': {
            'The Castro': 6,
            'Presidio': 15,
            'Sunset District': 15,
            'Mission District': 11,
            'Golden Gate Park': 7,
            'Russian Hill': 17
        },
        'Mission District': {
            'The Castro': 7,
            'Presidio': 25,
            'Sunset District': 24,
            'Haight-Ashbury': 12,
            'Golden Gate Park': 17,
            'Russian Hill': 15
        },
        'Golden Gate Park': {
            'The Castro': 13,
            'Presidio': 11,
            'Sunset District': 10,
            'Haight-Ashbury': 7,
            'Mission District': 17,
            'Russian Hill': 19
        },
        'Russian Hill': {
            'The Castro': 21,
            'Presidio': 14,
            'Sunset District': 23,
            'Haight-Ashbury': 17,
            'Mission District': 16,
            'Golden Gate Park': 21
        }
    }

    n = len(friends)
    s = Optimize()
    meet = [Bool(f"meet_{i}") for i in range(n)]
    start = [Int(f"start_{i}") for i in range(n)]
    end = [Int(f"end_{i}") for i in range(n)]
    order = [Int(f"order_{i}") for i in range(n)]

    for i in range(n):
        s.add(If(meet[i], And(order[i] >= 0, order[i] < n), order[i] == -1))

    for i in range(n):
        s.add(Implies(meet[i], start[i] >= available_start[friends[i]]))
        s.add(Implies(meet[i], end[i] == start[i] + min_durations[friends[i]]))
        s.add(Implies(meet[i], end[i] <= available_end[friends[i]]))

    for i in range(n):
        for j in range(i+1, n):
            s.add(Implies(And(meet[i], meet[j]), order[i] != order[j]))

    for k in range(1, n):
        cond_exists_k = Or([And(meet[i], order[i] == k) for i in range(n)])
        cond_exists_km1 = Or([And(meet[j], order[j] == k-1) for j in range(n)])
        s.add(Implies(cond_exists_k, cond_exists_km1))

    for i in range(n):
        loc_i = locations[friends[i]]
        cond0 = And(meet[i], order[i] == 0, start[i] >= 540 + travel_time_dict['The Castro'][loc_i])
        cond_other = Or([And(meet[j], order[j] == order[i]-1, 
                         start[i] >= end[j] + travel_time_dict[locations[friends[j]]][loc_i]) 
                        for j in range(n) if j != i])
        s.add(Implies(meet[i], Or(cond0, cond_other)))

    num_meetings = Sum([If(meet_i, 1, 0) for meet_i in meet])
    s.maximize(num_meetings)

    if s.check() == sat:
        m = s.model()
        scheduled_meetings = []
        for i in range(n):
            if is_true(m.evaluate(meet[i])):
                start_val = m.evaluate(start[i]).as_long()
                end_val = m.evaluate(end[i]).as_long()
                hours_start = start_val // 60
                minutes_start = start_val % 60
                hours_end = end_val // 60
                minutes_end = end_val % 60
                start_str = f"{hours_start:02d}:{minutes_start:02d}"
                end_str = f"{hours_end:02d}:{minutes_end:02d}"
                scheduled_meetings.append({
                    "action": "meet",
                    "person": friends[i],
                    "start_time": start_str,
                    "end_time": end_str
                })
        scheduled_meetings.sort(key=lambda x: x['start_time'])
        result = {"itinerary": scheduled_meetings}
        print("SOLUTION:")
        print(json.dumps(result, indent=2))
    else:
        print("SOLUTION:")
        print(json.dumps({"itinerary": []}, indent=2))

if __name__ == "__main__":
    main()