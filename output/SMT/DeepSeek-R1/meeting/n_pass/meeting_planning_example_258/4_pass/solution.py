from z3 import *

def minutes_to_time(minutes):
    total_minutes_from_midnight = 540 + minutes
    hours = total_minutes_from_midnight // 60
    mins = total_minutes_from_midnight % 60
    return f"{int(hours):02d}:{int(mins):02d}"

def main():
    names = ["Betty", "David", "Barbara"]
    
    travel_from_embarcadero = {
        "Betty": 20,   # to Presidio
        "David": 21,    # to Richmond District
        "Barbara": 6    # to Fisherman's Wharf
    }
    
    travel_time_between = {
        ("Betty", "David"): 7,
        ("Betty", "Barbara"): 19,
        ("David", "Betty"): 7,
        ("David", "Barbara"): 18,
        ("Barbara", "Betty"): 17,  # Corrected to 17 minutes
        ("Barbara", "David"): 18
    }
    
    available_start = {
        "Betty": 75,    # 10:15 AM
        "David": 240,   # 1:00 PM
        "Barbara": 15    # 9:15 AM
    }
    available_end = {
        "Betty": 750,   # 9:30 PM
        "David": 675,   # 8:15 PM
        "Barbara": 675   # 8:15 PM
    }
    duration_min = {
        "Betty": 45,
        "David": 90,
        "Barbara": 120
    }
    
    s = Optimize()
    
    start_time = {name: Int(f'start_{name}') for name in names}
    do_meet = {name: Bool(f'do_{name}') for name in names}
    end_time = {name: start_time[name] + duration_min[name] for name in names}
    
    before = {}
    for X in names:
        for Y in names:
            if X != Y:
                before[(X, Y)] = Bool(f'before_{X}_{Y}')
    
    for name in names:
        s.add(If(do_meet[name], 
                 And(start_time[name] >= available_start[name], 
                     end_time[name] <= available_end[name]), 
                 True))
        s.add(start_time[name] >= 0)
    
    for X in names:
        for Y in names:
            if X == Y:
                continue
            s.add(If(And(do_meet[X], do_meet[Y]), 
                   Or(before[(X, Y)], before[(Y, X)]), 
                   True))
            s.add(If(And(do_meet[X], do_meet[Y]), 
                   Not(And(before[(X, Y)], before[(Y, X)])), 
                   True))
            s.add(If(And(do_meet[X], do_meet[Y], before[(X, Y)]), 
                   start_time[Y] >= end_time[X] + travel_time_between[(X, Y)], 
                   True))
    
    for X in names:
        no_before = True
        for Y in names:
            if Y == X:
                continue
            no_before = And(no_before, 
                            If(do_meet[Y], 
                               Not(before[(Y, X)]), 
                               True))
        s.add(If(And(do_meet[X], no_before), 
               start_time[X] >= travel_from_embarcadero[X], 
               True))
    
    total_meetings = Sum([If(do_meet[name], 1, 0) for name in names])
    s.maximize(total_meetings)
    
    # Secondary objective: minimize sum of start times to find earliest possible meetings
    s.minimize(Sum([If(do_meet[name], start_time[name], 0) for name in names]))
    
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for name in names:
            if is_true(m[do_meet[name]]):
                start_val = m[start_time[name]].as_long()
                start_time_str = minutes_to_time(start_val)
                end_time_str = minutes_to_time(start_val + duration_min[name])
                itinerary.append({
                    "action": "meet", 
                    "person": name, 
                    "start_time": start_time_str, 
                    "end_time": end_time_str
                })
        
        itinerary.sort(key=lambda x: x['start_time'])
        print('SOLUTION:')
        print(f'{{"itinerary": {itinerary}}}')
    else:
        print("No solution found")

if __name__ == '__main__':
    main()