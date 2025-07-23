from z3 import *

def minutes_to_time(minutes):
    total_minutes_from_midnight = 540 + minutes  # 9:00 AM is 540 minutes from midnight
    hours = total_minutes_from_midnight // 60
    mins = total_minutes_from_midnight % 60
    return f"{int(hours):02d}:{int(mins):02d}"

def main():
    names = ["Betty", "David", "Barbara"]
    
    # Travel times from Embarcadero to each friend's location (in minutes)
    travel_from_embarcadero = {
        "Betty": 20,   # to Presidio
        "David": 21,    # to Richmond District
        "Barbara": 6     # to Fisherman's Wharf
    }
    
    # Asymmetric travel times between friends (in minutes)
    travel_time_between = {
        ("Betty", "David"): 7,
        ("Betty", "Barbara"): 19,
        ("David", "Betty"): 7,
        ("David", "Barbara"): 18,
        ("Barbara", "Betty"): 17,  # Corrected to 17 minutes
        ("Barbara", "David"): 18
    }
    
    # Availability windows (minutes after 9:00 AM)
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
    
    # Meeting durations (minutes)
    duration_min = {
        "Betty": 45,
        "David": 90,
        "Barbara": 120
    }
    
    # Create Z3 solver
    s = Optimize()
    
    # Decision variables
    start_time = {name: Int(f'start_{name}') for name in names}
    do_meet = {name: Bool(f'do_{name}') for name in names}
    end_time = {name: start_time[name] + duration_min[name] for name in names}
    
    # Ordering variables
    before = {}
    for X in names:
        for Y in names:
            if X != Y:
                before[(X, Y)] = Bool(f'before_{X}_{Y}')
    
    # Constraints
    for name in names:
        # If meeting occurs, it must be within availability window
        s.add(If(do_meet[name], 
                 And(start_time[name] >= available_start[name], 
                     end_time[name] <= available_end[name]), 
                 True))
        # Start time must be non-negative
        s.add(start_time[name] >= 0)
    
    # Meeting ordering and travel time constraints
    for X in names:
        for Y in names:
            if X == Y:
                continue
            # If both meetings occur, one must be before the other
            s.add(If(And(do_meet[X], do_meet[Y]), 
                   Or(before[(X, Y)], before[(Y, X)]), 
                   True))
            # Cannot be both before and after
            s.add(If(And(do_meet[X], do_meet[Y]), 
                   Not(And(before[(X, Y)], before[(Y, X)])), 
                   True))
            # If X before Y, Y must start after X ends plus travel time
            s.add(If(And(do_meet[X], do_meet[Y], before[(X, Y)]), 
                   start_time[Y] >= end_time[X] + travel_time_between[(X, Y)], 
                   True))
    
    # First meeting must allow time to travel from Embarcadero
    for X in names:
        is_first = True
        for Y in names:
            if Y == X:
                continue
            # If there's any meeting before X, then X is not first
            is_first = And(is_first, 
                           If(do_meet[Y], 
                              Not(before[(Y, X)]), 
                              True))
        s.add(If(And(do_meet[X], is_first), 
               start_time[X] >= travel_from_embarcadero[X], 
               True))
    
    # Maximize number of meetings
    total_meetings = Sum([If(do_meet[name], 1, 0) for name in names])
    s.maximize(total_meetings)
    
    # Secondary objective: minimize total start time
    s.minimize(Sum([If(do_meet[name], start_time[name], 0) for name in names]))
    
    # Solve and output
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
        
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: x['start_time'])
        print('SOLUTION:')
        print(f'{{"itinerary": {itinerary}}}')
    else:
        print("No solution found")

if __name__ == '__main__':
    main()