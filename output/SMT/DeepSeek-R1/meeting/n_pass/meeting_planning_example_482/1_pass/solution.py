from z3 import *
import json

def main():
    # Travel times between locations (including Haight-Ashbury)
    travel_times = {
        'HA': {'MD': 11, 'BV': 18, 'PH': 12, 'RH': 17, 'FW': 23},
        'MD': {'HA': 12, 'BV': 15, 'PH': 16, 'RH': 15, 'FW': 22},
        'BV': {'HA': 19, 'MD': 13, 'PH': 23, 'RH': 23, 'FW': 25},
        'PH': {'HA': 11, 'MD': 15, 'BV': 22, 'RH': 7, 'FW': 13},
        'RH': {'HA': 17, 'MD': 16, 'BV': 23, 'PH': 7, 'FW': 7},
        'FW': {'HA': 22, 'MD': 22, 'BV': 26, 'PH': 12, 'RH': 7}
    }
    
    # Meeting details: names, locations, availability, and durations
    names = ['Richard', 'Stephanie', 'Sandra', 'Brian', 'Jason']
    locs = ['PH', 'MD', 'BV', 'RH', 'FW']
    avail_start = [7*60+15, 8*60+15, 13*60, 12*60+15, 8*60+30]  # in minutes from midnight
    avail_end = [10*60+15, 13*60+45, 19*60+30, 16*60, 17*60+45]
    durations = [75, 90, 15, 120, 60]
    
    s = Solver()
    
    # Decision variables for meetings
    meet = [Bool(f"meet_{i}") for i in range(5)]
    start = [Int(f"start_{i}") for i in range(5)]
    end = [Int(f"end_{i}") for i in range(5)]
    
    # Before matrix: before[i][j] is True if meeting i is before meeting j
    before = [[Bool(f"before_{i}_{j}") if i != j else None for j in range(5)] for i in range(5)]
    
    # Meeting constraints
    for i in range(5):
        s.add(Implies(meet[i], 
                      And(start[i] >= avail_start[i],
                          end[i] <= avail_end[i],
                          end[i] == start[i] + durations[i])))
    
    # Pairwise constraints for meetings
    for i in range(5):
        for j in range(5):
            if i == j:
                continue
            s.add(Implies(And(meet[i], meet[j]),
                          And(Or(before[i][j], before[j][i]),
                              Not(And(before[i][j], before[j][i]))))
            s.add(Implies(And(meet[i], meet[j], before[i][j]),
                          start[j] >= end[i] + travel_times[locs[i]][locs[j]]))
    
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
    
    # First meeting constraints (travel from HA)
    for i in range(5):
        other_conditions = []
        for j in range(5):
            if i != j:
                other_conditions.append(Implies(meet[j], before[i][j]))
        is_first_i = And(meet[i], *other_conditions)
        s.add(Implies(is_first_i, start[i] >= 9*60 + travel_times['HA'][locs[i]]))
    
    # Maximize the number of meetings
    total_meetings = Sum([If(meet[i], 1, 0) for i in range(5)])
    s.maximize(total_meetings)
    
    # Solve and output
    if s.check() == sat:
        m = s.model()
        meetings_list = []
        for i in range(5):
            if m.evaluate(meet[i]):
                s_val = m.evaluate(start[i]).as_long()
                e_val = m.evaluate(end[i]).as_long()
                meetings_list.append((s_val, names[i], s_val, e_val))
        meetings_list.sort(key=lambda x: x[0])
        itinerary = []
        for meeting in meetings_list:
            s_minutes = meeting[2]
            e_minutes = meeting[3]
            start_time = f"{s_minutes // 60:02d}:{s_minutes % 60:02d}"
            end_time = f"{e_minutes // 60:02d}:{e_minutes % 60:02d}"
            itinerary.append({
                "action": "meet",
                "person": meeting[1],
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