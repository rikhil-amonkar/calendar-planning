from z3 import *
import json

def main():
    opt = Optimize()
    
    meetE = Bool('meetE')
    meetJ = Bool('meetJ')
    meetM = Bool('meetM')
    
    sE, eE = Real('sE'), Real('eE')
    sJ, eJ = Real('sJ'), Real('eJ')
    sM, eM = Real('sM'), Real('eM')
    
    orderE = Int('orderE')
    orderJ = Int('orderJ')
    orderM = Int('orderM')
    
    opt.add(If(meetE, And(orderE >= 0, orderE <= 2), orderE == -1))
    opt.add(If(meetJ, And(orderJ >= 0, orderJ <= 2), orderJ == -1))
    opt.add(If(meetM, And(orderM >= 0, orderM <= 2), orderM == -1))
    
    opt.add(If(And(meetE, meetJ), orderE != orderJ, True))
    opt.add(If(And(meetE, meetM), orderE != orderM, True))
    opt.add(If(And(meetJ, meetM), orderJ != orderM, True))
    
    durE = 105
    durJ = 120
    durM = 75
    
    avail_startE = 7*60 + 15
    avail_endE = 12*60
    avail_startJ = 8*60 + 15
    avail_endJ = 13*60
    avail_startM = 6*60 + 45
    avail_endM = 12*60 + 45
    
    opt.add(If(meetE, And(sE >= avail_startE, eE == sE + durE, eE <= avail_endE), True))
    opt.add(If(meetJ, And(sJ >= avail_startJ, eJ == sJ + durJ, eJ <= avail_endJ), True))
    opt.add(If(meetM, And(sM >= avail_startM, eM == sM + durM, eM <= avail_endM), True))
    
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
    
    locE = 'Presidio'
    locJ = 'Richmond District'
    locM = 'Financial District'
    loc_start = 'Fisherman\'s Wharf'
    
    meetings = [
        ('E', meetE, sE, eE, orderE, locE),
        ('J', meetJ, sJ, eJ, orderJ, locJ),
        ('M', meetM, sM, eM, orderM, locM)
    ]
    
    for name, meet, s, e, order, loc in meetings:
        travel_time = travel_times.get((loc_start, loc))
        if travel_time is not None:
            opt.add(If(And(meet, order == 0), s >= travel_time, True))
    
    for i in range(len(meetings)):
        name_i, meet_i, s_i, e_i, order_i, loc_i = meetings[i]
        for j in range(len(meetings)):
            if i == j:
                continue
            name_j, meet_j, s_j, e_j, order_j, loc_j = meetings[j]
            travel_time = travel_times.get((loc_i, loc_j))
            if travel_time is not None:
                opt.add(If(And(meet_i, meet_j, order_i < order_j), s_j >= e_i + travel_time, True))
    
    num_meetings = If(meetE, 1, 0) + If(meetJ, 1, 0) + If(meetM, 1, 0)
    opt.maximize(num_meetings)
    
    if opt.check() == sat:
        m = opt.model()
        itinerary = []
        
        def min_to_time(total_min):
            total_min = round(total_min)
            hours = total_min // 60
            minutes = total_min % 60
            abs_hours = 9 + hours
            return f"{abs_hours:02d}:{minutes:02d}"
        
        for name, meet, s, e, order, loc in meetings:
            if m.evaluate(meet) == True:
                s_val = m.evaluate(s)
                e_val = m.evaluate(e)
                if is_rational_value(s_val):
                    s_num = s_val.numerator_as_long()
                    s_den = s_val.denominator_as_long()
                    s_min = float(s_num) / float(s_den)
                else:
                    s_min = float(s_val.as_decimal(1)[:-1])
                if is_rational_value(e_val):
                    e_num = e_val.numerator_as_long()
                    e_den = e_val.denominator_as_long()
                    e_min = float(e_num) / float(e_den)
                else:
                    e_min = float(e_val.as_decimal(1)[:-1])
                start_time = min_to_time(s_min)
                end_time = min_to_time(e_min)
                person = {'E': 'Emily', 'J': 'Joseph', 'M': 'Melissa'}[name]
                itinerary.append({
                    "action": "meet",
                    "person": person,
                    "start_time": start_time,
                    "end_time": end_time
                })
        
        itinerary.sort(key=lambda x: x['start_time'])
        print("SOLUTION:")
        print(json.dumps({"itinerary": itinerary}))
    else:
        print("SOLUTION:")
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()