from z3 import *
import json

def main():
    # Initialize the optimizer
    opt = Optimize()
    
    # Boolean variables for whether we meet each friend
    meetE = Bool('meetE')
    meetJ = Bool('meetJ')
    meetM = Bool('meetM')
    
    # Real variables for start and end times (in minutes from 9:00 AM)
    sE, eE = Real('sE'), Real('eE')
    sJ, eJ = Real('sJ'), Real('eJ')
    sM, eM = Real('sM'), Real('eM')
    
    # Integer variables for the order of meetings (0,1,2 or -1 if not met)
    orderE = Int('orderE')
    orderJ = Int('orderJ')
    orderM = Int('orderM')
    
    # Constraints: if a friend is met, their order is between 0 and 2; otherwise, it's -1
    opt.add(If(meetE, And(orderE >= 0, orderE <= 2), orderE == -1)
    opt.add(If(meetJ, And(orderJ >= 0, orderJ <= 2), orderJ == -1)
    opt.add(If(meetM, And(orderM >= 0, orderM <= 2), orderM == -1)
    
    # If two friends are met, their orders must be distinct
    opt.add(If(And(meetE, meetJ), orderE != orderJ, True)
    opt.add(If(And(meetE, meetM), orderE != orderM, True)
    opt.add(If(And(meetJ, meetM), orderJ != orderM, True)
    
    # Durations for each meeting (in minutes)
    durE = 105
    durJ = 120
    durM = 75
    
    # Availability windows (in minutes from 9:00 AM)
    avail_startE = 7*60 + 15   # 16:15
    avail_endE = 12*60         # 21:00
    avail_startJ = 8*60 + 15   # 17:15
    avail_endJ = 13*60         # 22:00
    avail_startM = 6*60 + 45   # 15:45
    avail_endM = 12*60 + 45    # 21:45
    
    # Constraints for each friend if met
    opt.add(If(meetE, And(sE >= avail_startE, eE == sE + durE, eE <= avail_endE), True)
    opt.add(If(meetJ, And(sJ >= avail_startJ, eJ == sJ + durJ, eJ <= avail_endJ), True)
    opt.add(If(meetM, And(sM >= avail_startM, eM == sM + durM, eM <= avail_endM), True))
    
    # Travel times between locations (in minutes)
    travel_times = {
        ('Fisherman\'s Wharf', 'Presidio'): 17,
        ('Fisherman\'s Wharf', 'Richmond District'): 18,
        ('Fisherman\'s Wharf', 'Financial District'): 11,
        ('Presidio', 'Richmond District'): 7,
        ('Presidio', 'Financial District'): 23,
        ('Richmond District', 'Presidio'): 7,
        ('Richmond District', 'Financial District'): 22,
        ('Financial District', 'Presidio'): 22,
        ('Financial District', 'Richmond District'): 21
    }
    
    # Locations for each friend
    locE = 'Presidio'
    locJ = 'Richmond District'
    locM = 'Financial District'
    loc_start = 'Fisherman\'s Wharf'
    
    # Meetings data structure
    meetings = [
        ('E', meetE, sE, eE, orderE, locE),
        ('J', meetJ, sJ, eJ, orderJ, locJ),
        ('M', meetM, sM, eM, orderM, locM)
    ]
    
    # Constraint: if a meeting is first, its start time must be at least travel time from start
    for name, meet, s, e, order, loc in meetings:
        travel_time = travel_times.get((loc_start, loc))
        if travel_time is not None:
            opt.add(If(And(meet, order == 0), s >= travel_time, True)
    
    # Constraints for travel between consecutive meetings
    for i in range(len(meetings)):
        name_i, meet_i, s_i, e_i, order_i, loc_i = meetings[i]
        for j in range(len(meetings)):
            if i == j:
                continue
            name_j, meet_j, s_j, e_j, order_j, loc_j = meetings[j]
            travel_time = travel_times.get((loc_i, loc_j))
            if travel_time is not None:
                opt.add(If(And(meet_i, meet_j, order_i < order_j), 
                          s_j >= e_i + travel_time, 
                          True))
    
    # Objective: maximize the number of meetings
    num_meetings = If(meetE, 1, 0) + If(meetJ, 1, 0) + If(meetM, 1, 0)
    opt.maximize(num_meetings)
    
    # Solve the problem
    if opt.check() == sat:
        m = opt.model()
        itinerary = []
        
        # Helper function to convert minutes to HH:MM format
        def min_to_time(total_min):
            total_min = round(total_min)
            hours = total_min // 60
            minutes = total_min % 60
            abs_hours = 9 + hours
            return f"{abs_hours:02d}:{minutes:02d}"
        
        # Process each friend if met
        for name, meet, s, e, order, loc in meetings:
            if m.evaluate(meet) == True:
                s_val = m.evaluate(s)
                e_val = m.evaluate(e)
                # Convert Z3 values to float
                s_min = float(s_val.numerator_as_long()) / float(s_val.denominator_as_long())
                e_min = float(e_val.numerator_as_long()) / float(e_val.denominator_as_long())
                start_time = min_to_time(s_min)
                end_time = min_to_time(e_min)
                person = {'E': 'Emily', 'J': 'Joseph', 'M': 'Melissa'}[name]
                itinerary.append({
                    "action": "meet",
                    "person": person,
                    "start_time": start_time,
                    "end_time": end_time
                })
        
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: x['start_time'])
        print("SOLUTION:")
        print(json.dumps({"itinerary": itinerary}))
    else:
        print("SOLUTION:")
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()