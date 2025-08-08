from z3 import *
import json

def main():
    # Travel times between locations
    travel_times = {
        'HA': {'MD': 11, 'BV': 18, 'PH': 12, 'RH': 17, 'FW': 23},
        'MD': {'HA': 12, 'BV': 15, 'PH': 16, 'RH': 15, 'FW': 22},
        'BV': {'HA': 19, 'MD': 13, 'PH': 23, 'RH': 23, 'FW': 25},
        'PH': {'HA': 11, 'MD': 15, 'BV': 22, 'RH': 7, 'FW': 13},
        'RH': {'HA': 17, 'MD': 16, 'BV': 23, 'PH': 7, 'FW': 7},
        'FW': {'HA': 22, 'MD': 22, 'BV': 26, 'PH': 12, 'RH': 7}
    }
    
    # Meeting details
    names = ['Richard', 'Stephanie', 'Sandra', 'Brian', 'Jason']
    locs = ['PH', 'MD', 'BV', 'RH', 'FW']
    avail_start = [7*60+15, 8*60+15, 13*60, 12*60+15, 8*60+30]
    avail_end = [10*60+15, 13*60+45, 19*60+30, 16*60, 17*60+45]
    durations = [75, 90, 15, 120, 60]
    
    # Use Optimize instead of Solver
    s = Optimize()
    
    # Decision variables
    meet = [Bool(f"meet_{i}") for i in range(5)]
    start = [Int(f"start_{i}") for i in range(5)]
    end = [Int(f"end_{i}") for i in range(5)]
    before = [[Bool(f"before_{i}_{j}") for j in range(5)] for i in range(5)]
    
    # Meeting constraints
    for i in range(5):
        s.add(Implies(meet[i], 
                      And(start[i] >= avail_start[i],
                          end[i] <= avail_end[i],
                          end[i] == start[i] + durations[i])))
    
    # Pairwise constraints
    for i in range(5):
        for j in range(5):
            if i == j:
                continue
            cond = And(meet[i], meet[j])
            # Mutual exclusion
            s.add(Implies(cond, before[i][j] != before[j][i]))
            # One must be before the other
            s.add(Implies(cond, Or(before[i][j], before[j][i])))
            # Travel time constraints
            s.add(Implies(And(cond, before[i][j]), 
                          start[j] >= end[i] + travel_times[locs[i]][locs[j]]))
            s.add(Implies(And(cond, before[j][i]), 
                          start[i] >= end[j] + travel_times[locs[j]][locs[i]]))
    
    # Transitivity constraints
    for i in range(5):
        for j in range(5):
            if i == j:
                continue
            for k in range(5):
                if i == k or j == k:
                    continue
                s.add(Implies(And(meet[i], meet[j], meet[k], before[i][j], before[j][k]),
                              before[i][k]))
    
    # First meeting constraints
    for i in range(5):
        other_conditions = []
        for j in range(5):
            if i != j:
                other_conditions.append(Implies(meet[j], before[i][j]))
        is_first_i = And(meet[i], *other_conditions)
        s.add(Implies(is_first_i, start[i] >= 9*60 + travel_times['HA'][locs[i]]))
    
    # Maximize meetings using Optimize
    s.maximize(Sum([If(meet[i], 1, 0) for i in range(5)]))
    
    # Solve and format output
    if s.check() == sat:
        m = s.model()
        meetings = []
        for i in range(5):
            if is_true(m[meet[i]]):
                s_val = m.evaluate(start[i]).as_long()
                e_val = m.evaluate(end[i]).as_long()
                meetings.append((s_val, names[i], s_val, e_val))
        meetings.sort(key=lambda x: x[0])
        itinerary = []
        for mtg in meetings:
            start_hr, start_min = divmod(mtg[2], 60)
            end_hr, end_min = divmod(mtg[3], 60)
            start_time = f"{start_hr:02d}:{start_min:02d}"
            end_time = f"{end_hr:02d}:{end_min:02d}"
            itinerary.append({
                "action": "meet",
                "person": mtg[1],
                "start_time": start_time,
                "end_time": end_time
            })
        print('SOLUTION:')
        print(json.dumps({"itinerary": itinerary}))
    else:
        print("SOLUTION:")
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()