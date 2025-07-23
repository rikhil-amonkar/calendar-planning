from z3 import *
import json

def format_time(minutes):
    hours = minutes // 60
    minutes_remain = minutes % 60
    return f"{hours:02d}:{minutes_remain:02d}"

def main():
    meetings = [
        {"name": "Start", "loc": "Bayview", "min_start": 540, "max_end": 540, "duration": 0},
        {"name": "Barbara", "loc": "North Beach", "min_start": 825, "max_end": 1215, "duration": 60},
        {"name": "Margaret", "loc": "Presidio", "min_start": 615, "max_end": 915, "duration": 30},
        {"name": "Kevin", "loc": "Haight-Ashbury", "min_start": 1200, "max_end": 1245, "duration": 30},
        {"name": "Kimberly", "loc": "Union Square", "min_start": 465, "max_end": 1005, "duration": 30}
    ]
    
    travel_times_dict = {
        'Bayview': {'North Beach': 21, 'Presidio': 31, 'Haight-Ashbury': 19, 'Union Square': 17},
        'North Beach': {'Bayview': 22, 'Presidio': 17, 'Haight-Ashbury': 18, 'Union Square': 7},
        'Presidio': {'Bayview': 31, 'North Beach': 18, 'Haight-Ashbury': 15, 'Union Square': 22},
        'Haight-Ashbury': {'Bayview': 18, 'North Beach': 19, 'Presidio': 15, 'Union Square': 17},
        'Union Square': {'Bayview': 15, 'North Beach': 10, 'Presidio': 24, 'Haight-Ashbury': 18}
    }
    
    s = Solver()
    
    S = [Int(f'S_{i}') for i in range(5)]
    E = [Int(f'E_{i}') for i in range(5)]
    
    for i in range(5):
        if i == 0:
            s.add(S[0] == 540)
            s.add(E[0] == 540)
        else:
            s.add(S[i] >= meetings[i]['min_start'])
            s.add(E[i] == S[i] + meetings[i]['duration'])
            s.add(E[i] <= meetings[i]['max_end'])
            s.add(S[i] >= 0)
            s.add(E[i] >= 0)
    
    before = {}
    for i in range(5):
        for j in range(5):
            if i != j:
                before[(i, j)] = Bool(f"before_{i}_{j}")
    
    for i in range(5):
        for j in range(i+1, 5):
            s.add(before[(i, j)] == Not(before[(j, i)]))
    
    for j in range(1, 5):
        s.add(before[(0, j)])
    
    for i in range(5):
        for j in range(5):
            if i == j:
                continue
            for k in range(5):
                if i == k or j == k:
                    continue
                s.add(Implies(And(before[(i, j)], before[(j, k)]), before[(i, k)]))
    
    for i in range(5):
        for j in range(5):
            if i == j:
                continue
            loc_i = meetings[i]['loc']
            loc_j = meetings[j]['loc']
            travel = travel_times_dict[loc_i][loc_j]
            s.add(Implies(before[(i, j)], S[j] >= E[i] + travel))
    
    if s.check() == sat:
        m = s.model()
        schedule = []
        for i in range(1, 5):
            start_val = m.evaluate(S[i]).as_long()
            end_val = m.evaluate(E[i]).as_long()
            schedule.append((meetings[i]['name'], start_val, end_val))
        schedule.sort(key=lambda x: x[1])
        itinerary = []
        for (name, start, end) in schedule:
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": format_time(start),
                "end_time": format_time(end)
            })
        result = {"itinerary": itinerary}
        print("SOLUTION:")
        print(json.dumps(result))
    else:
        print("No feasible schedule found.")

if __name__ == "__main__":
    main()