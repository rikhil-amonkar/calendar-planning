from z3 import *
import json

def main():
    travel_time = {
        ('H', 'F'): 23,
        ('H', 'R'): 10,
        ('H', 'M'): 11,
        ('H', 'B'): 18,
        ('F', 'H'): 22,
        ('F', 'R'): 18,
        ('F', 'M'): 22,
        ('F', 'B'): 26,
        ('R', 'H'): 10,
        ('R', 'F'): 18,
        ('R', 'M'): 20,
        ('R', 'B'): 26,
        ('M', 'H'): 12,
        ('M', 'F'): 22,
        ('M', 'R'): 20,
        ('M', 'B'): 15,
        ('B', 'H'): 19,
        ('B', 'F'): 25,
        ('B', 'R'): 25,
        ('B', 'M'): 13
    }

    friends = {
        'Sarah': {'loc': 'F', 'start_avail': 345, 'end_avail': 510, 'duration': 105},
        'Mary': {'loc': 'R', 'start_avail': 240, 'end_avail': 615, 'duration': 75},
        'Helen': {'loc': 'M', 'start_avail': 765, 'end_avail': 810, 'duration': 30}
    }

    s = {}
    end = {}
    pos = {}
    for name in friends:
        s[name] = Int(f's_{name}')
        end[name] = s[name] + friends[name]['duration']
        pos[name] = Int(f'pos_{name}')

    solver = Solver()

    for name in friends:
        solver.add(pos[name] >= 0, pos[name] <= 2)

    solver.add(Distinct([pos[name] for name in friends]))

    for name in friends:
        info = friends[name]
        solver.add(s[name] >= info['start_avail'])
        solver.add(s[name] + info['duration'] <= info['end_avail'])

    for name in friends:
        loc = friends[name]['loc']
        solver.add(Implies(pos[name] == 0, s[name] >= travel_time[('H', loc)]))

    for i in range(0, 2):
        for A in friends:
            for B in friends:
                if A == B:
                    continue
                loc_A = friends[A]['loc']
                loc_B = friends[B]['loc']
                cond = And(pos[A] == i, pos[B] == i+1)
                travel = travel_time.get((loc_A, loc_B))
                if travel is not None:
                    solver.add(Implies(cond, s[B] >= end[A] + travel))

    if solver.check() == sat:
        m = solver.model()
        schedule = []
        pos_vals = {}
        for name in friends:
            start_val = m.eval(s[name]).as_long()
            end_val = start_val + friends[name]['duration']
            total_minutes_start = start_val
            hours_start = total_minutes_start // 60
            minutes_start = total_minutes_start % 60
            start_str = f"{hours_start:02d}:{minutes_start:02d}"
            total_minutes_end = end_val
            hours_end = total_minutes_end // 60
            minutes_end = total_minutes_end % 60
            end_str = f"{hours_end:02d}:{minutes_end:02d}"
            schedule.append({
                "action": "meet",
                "person": name,
                "start_time": start_str,
                "end_time": end_str
            })
            pos_vals[name] = m.eval(pos[name]).as_long()
        
        schedule_sorted = sorted(schedule, key=lambda x: pos_vals[x['person']])
        result = {"itinerary": schedule_sorted}
        print(json.dumps(result))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()