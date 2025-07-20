from z3 import *

def main():
    friends = ['Helen', 'Kevin', 'Betty', 'Amanda']
    meet = {f: Bool(f'meet_{f}') for f in friends}
    start = {f: Int(f'start_{f}') for f in friends}
    order = {f: Int(f'order_{f}') for f in friends}
    
    loc = {
        'Helen': 'North Beach',
        'Kevin': 'Mission District',
        'Betty': 'Financial District',
        'Amanda': 'Alamo Square'
    }
    
    travel_time = {
        ('Pacific Heights', 'North Beach'): 9,
        ('Pacific Heights', 'Financial District'): 13,
        ('Pacific Heights', 'Alamo Square'): 10,
        ('Pacific Heights', 'Mission District'): 15,
        ('North Beach', 'Financial District'): 8,
        ('North Beach', 'Alamo Square'): 16,
        ('North Beach', 'Mission District'): 18,
        ('Financial District', 'North Beach'): 7,
        ('Financial District', 'Alamo Square'): 17,
        ('Financial District', 'Mission District'): 17,
        ('Alamo Square', 'North Beach'): 15,
        ('Alamo Square', 'Financial District'): 17,
        ('Alamo Square', 'Mission District'): 10,
        ('Mission District', 'North Beach'): 17,
        ('Mission District', 'Financial District'): 17,
        ('Mission District', 'Alamo Square'): 11
    }
    
    def get_travel_time(from_loc, to_loc):
        if from_loc == to_loc:
            return 0
        key = (from_loc, to_loc)
        return travel_time.get(key, 0)
    
    dur = {
        'Helen': 15,
        'Kevin': 45,
        'Betty': 90,
        'Amanda': 60
    }
    
    window_start = {
        'Helen': 0,         # 9:00 AM
        'Kevin': 105,        # 10:45 AM
        'Betty': 600,        # 7:00 PM
        'Amanda': 645        # 7:45 PM
    }
    
    window_end = {
        'Helen': 480,        # 5:00 PM
        'Kevin': 345,        # 2:45 PM
        'Betty': 765,        # 9:45 PM
        'Amanda': 720        # 9:00 PM
    }
    
    s = Optimize()
    
    for f in friends:
        s.add(Implies(meet[f], And(start[f] >= window_start[f], start[f] + dur[f] <= window_end[f])))
        s.add(Implies(meet[f], And(order[f] >= 0, order[f] < 4)))
        s.add(Implies(Not(meet[f]), order[f] == -1))
        s.add(Implies(meet[f], start[f] >= get_travel_time('Pacific Heights', loc[f])))
    
    for i in range(len(friends)):
        for j in range(i + 1, len(friends)):
            f1 = friends[i]
            f2 = friends[j]
            both_met = And(meet[f1], meet[f2])
            s.add(Implies(both_met, order[f1] != order[f2]))
            cond = If(order[f1] < order[f2],
                      start[f2] >= start[f1] + dur[f1] + get_travel_time(loc[f1], loc[f2]),
                      start[f1] >= start[f2] + dur[f2] + get_travel_time(loc[f2], loc[f1]))
            s.add(Implies(both_met, cond))
    
    obj = Sum([If(meet[f], 1, 0) for f in friends])
    s.maximize(obj)
    
    if s.check() == sat:
        m = s.model()
        total_meetings = 0
        schedule = []
        for f in friends:
            if m[meet[f]]:
                total_meetings += 1
                start_min = m[start[f]].as_long()
                hours = 9 + start_min // 60
                minutes = start_min % 60
                end_min = start_min + dur[f]
                end_hours = 9 + end_min // 60
                end_minutes = end_min % 60
                schedule.append(f"Meet {f} at {loc[f]} from {hours}:{minutes:02d} to {end_hours}:{end_minutes:02d}")
        print(f"Total meetings: {total_meetings}")
        for event in schedule:
            print(event)
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()