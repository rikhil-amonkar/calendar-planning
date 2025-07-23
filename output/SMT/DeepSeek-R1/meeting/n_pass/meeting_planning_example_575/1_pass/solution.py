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
        'Rebecca': 555,   # 6:15 PM
        'Linda': 390,      # 3:30 PM
        'Elizabeth': 495,   # 5:15 PM
        'William': 255,     # 1:15 PM
        'Robert': 315,      # 2:15 PM
        'Mark': 60          # 10:00 AM
    }
    available_end = {
        'Rebecca': 705,    # 8:45 PM
        'Linda': 645,       # 7:45 PM
        'Elizabeth': 630,   # 7:30 PM
        'William': 630,     # 7:30 PM
        'Robert': 750,      # 9:30 PM
        'Mark': 735         # 9:15 PM
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

    s = Solver()
    meet = [Bool(f"meet_{i}") for i in range(len(friends))]
    start = [Int(f"start_{i}") for i in range(len(friends))]
    end = [Int(f"end_{i}") for i in range(len(friends))]

    for i in range(len(friends)):
        s.add(Implies(meet[i], start[i] >= available_start[friends[i]]))
        s.add(Implies(meet[i], end[i] == start[i] + min_durations[friends[i]]))
        s.add(Implies(meet[i], end[i] <= available_end[friends[i]]))
        from_loc = 'The Castro'
        to_loc = locations[friends[i]]
        travel_time = travel_time_dict[from_loc][to_loc]
        s.add(Implies(meet[i], start[i] >= travel_time))

    for i in range(len(friends)):
        for j in range(i+1, len(friends)):
            loc_i = locations[friends[i]]
            loc_j = locations[friends[j]]
            travel_ij = travel_time_dict[loc_i][loc_j]
            travel_ji = travel_time_dict[loc_j][loc_i]
            s.add(Implies(And(meet[i], meet[j]),
                          Or(start[j] >= end[i] + travel_ij, 
                             start[i] >= end[j] + travel_ji)))

    opt = Optimize()
    for c in s.assertions():
        opt.add(c)
    num_meetings = Sum([If(meet_i, 1, 0) for meet_i in meet])
    h = opt.maximize(num_meetings)
    if opt.check() == sat:
        model = opt.model()
        scheduled_meetings = []
        for i in range(len(friends)):
            if model.evaluate(meet[i]):
                start_val = model.evaluate(start[i]).as_long()
                end_val = model.evaluate(end[i]).as_long()
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