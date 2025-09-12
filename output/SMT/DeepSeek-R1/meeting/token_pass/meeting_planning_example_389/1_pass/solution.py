import json
from z3 import *

def main():
    travel_times = {
        'Haight-Ashbury': {
            'Fisherman\'s Wharf': 23,
            'Richmond District': 10,
            'Mission District': 11,
            'Bayview': 18
        },
        'Fisherman\'s Wharf': {
            'Haight-Ashbury': 22,
            'Richmond District': 18,
            'Mission District': 22,
            'Bayview': 26
        },
        'Richmond District': {
            'Haight-Ashbury': 10,
            'Fisherman\'s Wharf': 18,
            'Mission District': 20,
            'Bayview': 26
        },
        'Mission District': {
            'Haight-Ashbury': 12,
            'Fisherman\'s Wharf': 22,
            'Richmond District': 20,
            'Bayview': 15
        },
        'Bayview': {
            'Haight-Ashbury': 19,
            'Fisherman\'s Wharf': 25,
            'Richmond District': 25,
            'Mission District': 13
        }
    }

    persons = [
        {'name': 'Sarah', 'loc': 'Fisherman\'s Wharf', 'start_avail': 345, 'end_avail': 510, 'min_dur': 105},
        {'name': 'Mary', 'loc': 'Richmond District', 'start_avail': 240, 'end_avail': 615, 'min_dur': 75},
        {'name': 'Helen', 'loc': 'Mission District', 'start_avail': 765, 'end_avail': 810, 'min_dur': 30},
        {'name': 'Thomas', 'loc': 'Bayview', 'start_avail': 375, 'end_avail': 585, 'min_dur': 120}
    ]

    n = len(persons)
    scheduled_flags = [Bool(f"scheduled_{i}") for i in range(n)]
    start_vars = [Int(f"start_{i}") for i in range(n)]
    before = [[Bool(f"before_{i}_{j}") for j in range(n)] for i in range(n)]

    opt = Optimize()

    for i in range(n):
        for j in range(n):
            if i == j:
                continue
            opt.add(Implies(And(scheduled_flags[i], scheduled_flags[j]), Or(before[i][j], before[j][i])))
            opt.add(Not(And(before[i][j], before[j][i])))

    for i in range(n):
        for j in range(n):
            if i == j:
                continue
            travel_time = travel_times[persons[i]['loc']][persons[j]['loc']]
            opt.add(Implies(And(scheduled_flags[i], scheduled_flags[j], before[i][j]),
                            start_vars[j] >= start_vars[i] + persons[i]['min_dur'] + travel_time))

    for i in range(n):
        opt.add(Implies(scheduled_flags[i], start_vars[i] >= persons[i]['start_avail']))
        opt.add(Implies(scheduled_flags[i], start_vars[i] + persons[i]['min_dur'] <= persons[i]['end_avail']))
        opt.add(Implies(scheduled_flags[i], start_vars[i] >= travel_times['Haight-Ashbury'][persons[i]['loc']]))

    opt.maximize(Sum([If(scheduled_flags[i], 1, 0) for i in range(n)]))

    if opt.check() == sat:
        m = opt.model()
        scheduled_meetings = []
        for i in range(n):
            if is_true(m.evaluate(scheduled_flags[i])):
                start_val = m.evaluate(start_vars[i])
                start_minutes = start_val.as_long()
                hours = start_minutes // 60
                minutes = start_minutes % 60
                start_time_str = f"{hours}:{minutes:02d}"
                end_minutes = start_minutes + persons[i]['min_dur']
                hours_end = end_minutes // 60
                minutes_end = end_minutes % 60
                end_time_str = f"{hours_end}:{minutes_end:02d}"
                scheduled_meetings.append({
                    "action": "meet",
                    "location": persons[i]['loc'],
                    "person": persons[i]['name'],
                    "start_time": start_time_str,
                    "end_time": end_time_str
                })
        scheduled_meetings.sort(key=lambda x: x['start_time'])
        result = {"itinerary": scheduled_meetings}
        print(json.dumps(result))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()