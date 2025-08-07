from z3 import *
import itertools
import json

def main():
    meetings = [
        {"name": "Mary", "location": "RD", "start_window": 240, "end_window": 615, "duration": 75},
        {"name": "Sarah", "location": "FW", "start_window": 345, "end_window": 510, "duration": 105},
        {"name": "Thomas", "location": "BV", "start_window": 375, "end_window": 585, "duration": 120},
        {"name": "Helen", "location": "MD", "start_window": 765, "end_window": 810, "duration": 30}
    ]

    travel_times = {
        'HA': {'RD': 10, 'FW': 23, 'BV': 18, 'MD': 11},
        'RD': {'HA': 10, 'FW': 18, 'BV': 26, 'MD': 20},
        'FW': {'HA': 22, 'RD': 18, 'BV': 26, 'MD': 22},
        'BV': {'HA': 19, 'RD': 25, 'FW': 25, 'MD': 13},
        'MD': {'HA': 12, 'RD': 20, 'FW': 22, 'BV': 15}
    }

    meeting_indices = [0, 1, 2, 3]
    solution_found = False
    result_schedule = None

    for k in [4, 3, 2, 1]:
        if solution_found:
            break
        for subset in itertools.combinations(meeting_indices, k):
            if solution_found:
                break
            orders = []
            if 3 in subset:
                non_helen = [idx for idx in subset if idx != 3]
                for perm in itertools.permutations(non_helen):
                    orders.append(perm + (3,))
            else:
                for perm in itertools.permutations(subset):
                    orders.append(perm)
            for order in orders:
                s = Solver()
                k_val = len(order)
                start_vars = [Int(f'start_{i}') for i in range(k_val)]
                first_meeting = meetings[order[0]]
                travel0 = travel_times['HA'][first_meeting['location']]
                s.add(start_vars[0] >= travel0)
                for i in range(1, k_val):
                    prev_meeting = meetings[order[i-1]]
                    curr_meeting = meetings[order[i]]
                    travel_time_ij = travel_times[prev_meeting['location']][curr_meeting['location']]
                    s.add(start_vars[i] >= start_vars[i-1] + prev_meeting['duration'] + travel_time_ij)
                for i in range(k_val):
                    meeting = meetings[order[i]]
                    s.add(start_vars[i] >= meeting['start_window'])
                    s.add(start_vars[i] + meeting['duration'] <= meeting['end_window'])
                if s.check() == sat:
                    model = s.model()
                    start_times = [model.eval(start_vars[i]).as_long() for i in range(k_val)]
                    schedule = []
                    for i in range(k_val):
                        meeting_idx = order[i]
                        meeting = meetings[meeting_idx]
                        start_minutes = start_times[i]
                        end_minutes = start_minutes + meeting['duration']
                        start_hour = start_minutes // 60
                        start_minute = start_minutes % 60
                        end_hour = end_minutes // 60
                        end_minute = end_minutes % 60
                        start_str = f"{start_hour:02d}:{start_minute:02d}"
                        end_str = f"{end_hour:02d}:{end_minute:02d}"
                        schedule.append({
                            "action": "meet",
                            "person": meeting['name'],
                            "start_time": start_str,
                            "end_time": end_str
                        })
                    result_schedule = schedule
                    solution_found = True
                    break
        if solution_found:
            break

    if result_schedule is None:
        result_schedule = []

    output = {"itinerary": result_schedule}
    print("SOLUTION:")
    print(json.dumps(output))

if __name__ == "__main__":
    main()