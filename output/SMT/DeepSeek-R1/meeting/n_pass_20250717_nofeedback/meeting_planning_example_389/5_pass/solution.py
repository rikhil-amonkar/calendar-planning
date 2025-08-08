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
    
    friends = ['Sarah', 'Mary', 'Helen', 'Thomas']
    f_to_loc = {
        'Sarah': 'F',
        'Mary': 'R',
        'Helen': 'M',
        'Thomas': 'B'
    }
    
    avail = {
        'Sarah': (345, 510, 105),    # 5:45 AM to 8:30 AM (duration 105 min)
        'Mary': (240, 615, 75),      # 4:00 AM to 10:15 AM (duration 75 min)
        'Helen': (765, 810, 30),     # 12:45 PM to 1:30 PM (duration 30 min)
        'Thomas': (375, 585, 120)    # 6:15 AM to 9:45 AM (duration 120 min)
    }
    
    meet = {f: Bool(f'meet_{f}') for f in friends}
    s = {f: Int(f's_{f}') for f in friends}  # Start time in minutes from midnight
    pos = {f: Int(f'pos_{f}') for f in friends}  # Position in itinerary (0,1,2)
    
    opt = Optimize()
    
    num_meet = Int('num_meet')
    opt.add(num_meet == Sum([If(meet[f], 1, 0) for f in friends]))
    opt.maximize(num_meet)
    
    for f in friends:
        opt.add(Implies(meet[f], And(pos[f] >= 0, pos[f] <= 2)))
        start_avail, end_avail, dur = avail[f]
        opt.add(Implies(meet[f], And(s[f] >= start_avail, s[f] + dur <= end_avail)))
        opt.add(Implies(meet[f], pos[f] < num_meet))
    
    for i in range(0, 3):
        opt.add(Sum([If(And(meet[f], pos[f] == i), 1, 0) for f in friends]) <= 1)
    
    for f in friends:
        opt.add(Implies(And(meet[f], pos[f] == 0), s[f] >= 540 + travel_time[('H', f_to_loc[f])]))
        
        for i in [1, 2]:
            for f_prev in friends:
                if f_prev == f:
                    continue
                opt.add(Implies(
                    And(meet[f], meet[f_prev], pos[f] == i, pos[f_prev] == i-1),
                    s[f] >= s[f_prev] + avail[f_prev][2] + travel_time[(f_to_loc[f_prev], f_to_loc[f])]
                ))
    
    # Return to Haight-Ashbury by 2:00 PM (840 minutes)
    for f in friends:
        opt.add(Implies(And(meet[f], pos[f] == num_meet - 1),
                           s[f] + avail[f][2] + travel_time[(f_to_loc[f], 'H')] <= 840))
    
    if opt.check() == sat:
        m = opt.model()
        schedule = []
        for f in friends:
            if is_true(m.eval(meet[f])):
                start_val = m.eval(s[f]).as_long()
                dur = avail[f][2]
                hours_start = start_val // 60
                minutes_start = start_val % 60
                start_str = f"{hours_start:02d}:{minutes_start:02d}"
                
                end_val = start_val + dur
                hours_end = end_val // 60
                minutes_end = end_val % 60
                end_str = f"{hours_end:02d}:{minutes_end:02d}"
                
                schedule.append({
                    "action": "meet",
                    "person": f,
                    "start_time": start_str,
                    "end_time": end_str
                })
        schedule_sorted = sorted(schedule, key=lambda x: x['start_time'])
        result = {"itinerary": schedule_sorted}
        print(json.dumps(result))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()