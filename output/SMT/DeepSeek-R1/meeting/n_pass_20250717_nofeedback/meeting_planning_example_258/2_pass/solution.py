from z3 import *

def minutes_to_time(minutes):
    total_minutes = minutes
    hours = total_minutes // 60
    mins = total_minutes % 60
    time_str = f"{int(hours):02d}:{int(mins):02d}"
    return time_str

def main():
    # Define names
    names = ["Betty", "David", "Barbara"]
    
    # Travel times from Embarcadero to each location
    travel_from_embarcadero = {
        "Betty": 20,   # to Presidio
        "David": 21,    # to Richmond District
        "Barbara": 6    # to Fisherman's Wharf
    }
    
    # Travel times between locations
    travel_time_between = {
        ("Betty", "David"): 7,    # Presidio to Richmond District
        ("Betty", "Barbara"): 19,  # Presidio to Fisherman's Wharf
        ("David", "Betty"): 7,     # Richmond District to Presidio
        ("David", "Barbara"): 18,   # Richmond District to Fisherman's Wharf
        ("Barbara", "Betty"): 17,  # Fisherman's Wharf to Presidio
        ("Barbara", "David"): 18    # Fisherman's Wharf to Richmond District
    }
    
    # Availability and duration constraints (in minutes from 9:00 AM)
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
    
    # Create solver
    s = Optimize()
    
    # Meeting start times (integers)
    start_time = {name: Int(f'start_{name}') for name in names}
    # Boolean for whether we meet each friend
    do_meet = {name: Bool(f'do_{name}') for name in names}
    # End times
    end_time = {}
    for name in names:
        end_time[name] = start_time[name] + duration_min[name]
    
    # Pairwise booleans for ordering
    # b_XY: X before Y
    before = {}
    for X in names:
        for Y in names:
            if X != Y:
                before[(X, Y)] = Bool(f'before_{X}_{Y}')
    
    # Constraints for each meeting
    for name in names:
        # If meeting, ensure within availability window
        s.add(If(do_meet[name], 
                 And(start_time[name] >= available_start[name], 
                     end_time[name] <= available_end[name]), 
                 True))
        # Start time must be non-negative
        s.add(start_time[name] >= 0)
    
    # For each pair (X, Y) with X != Y
    for X in names:
        for Y in names:
            if X == Y:
                continue
            # If both meetings happen, then either X before Y or Y before X, but not both
            s.add(If(And(do_meet[X], do_meet[Y]), 
                   Or(before[(X, Y)], before[(Y, X)]), 
                   True))
            s.add(If(And(do_meet[X], do_meet[Y]), 
                   Not(And(before[(X, Y)], before[(Y, X)])), 
                   True))
            # If X before Y, then Y must start at least after X ends plus travel time
            s.add(If(And(do_meet[X], do_meet[Y], before[(X, Y)]), 
                   start_time[Y] >= end_time[X] + travel_time_between[(X, Y)], 
                   True))
    
    # First meeting constraints
    for X in names:
        # X is first if no other meeting Y (that is happening) is before X
        no_before = True
        for Y in names:
            if Y == X:
                continue
            no_before = And(no_before, 
                            If(do_meet[Y], 
                               Not(before[(Y, X)]), 
                               True))
        # If X is the first meeting and is happening, then start time must be at least travel from Embarcadero
        s.add(If(And(do_meet[X], no_before), 
               start_time[X] >= travel_from_embarcadero[X], 
               True))
    
    # Maximize the number of meetings
    total_meetings = Sum([If(do_meet[name], 1, 0) for name in names])
    s.maximize(total_meetings)
    
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