from z3 import *
import json

def Max(a, b):
    return If(a >= b, a, b)

def minutes_to_time(m):
    h = m // 60
    mins = m % 60
    return f"{h}:{mins:02d}"

bayview_arrival = 9 * 60           
union_travel_from_bayview = 17     
presidio_travel_from_bayview = 31  
union_to_presidio = 24             
presidio_to_union = 22             
meeting_min = 120                  

richard_avail_start = 8 * 60 + 45  
richard_avail_end = 13 * 60        

charles_avail_start = 9 * 60 + 45  
charles_avail_end = 13 * 60        

opt = Optimize()

R_start = Int('R_start')  
R_end = Int('R_end')      
C_start = Int('C_start')  
C_end = Int('C_end')      

attend_R = Bool('attend_R')
attend_C = Bool('attend_C')

order_R_first = Bool('order_R_first')

opt.add(Implies(Not(attend_R), And(R_start == 0, R_end == 0)))
opt.add(Implies(Not(attend_C), And(C_start == 0, C_end == 0)))

opt.add(Implies(attend_R, R_end - R_start >= meeting_min))
opt.add(Implies(attend_R, R_end <= richard_avail_end))
opt.add(Implies(attend_R,
    And(
        R_start >= If(Or(Not(attend_C), order_R_first), bayview_arrival + union_travel_from_bayview, C_end + presidio_to_union),
        R_start >= richard_avail_start  
    )
))

opt.add(Implies(attend_C, C_end - C_start >= meeting_min))
opt.add(Implies(attend_C, C_end <= charles_avail_end))
opt.add(Implies(attend_C,
    And(
        C_start >= If(Or(Not(attend_R), Not(order_R_first)),
                      Max(bayview_arrival + presidio_travel_from_bayview, charles_avail_start),
                      R_end + union_to_presidio),
        C_start >= charles_avail_start  
    )
))

opt.add(Implies(And(attend_R, attend_C, order_R_first),
    And(
        R_start >= bayview_arrival + union_travel_from_bayview,
        C_start >= R_end + union_to_presidio
    )
))
opt.add(Implies(And(attend_R, attend_C, Not(order_R_first)),
    And(
        C_start >= Max(bayview_arrival + presidio_travel_from_bayview, charles_avail_start),
        R_start >= C_end + presidio_to_union
    )
))

meetings_count = If(attend_R, 1, 0) + If(attend_C, 1, 0)
total_duration = If(attend_R, R_end - R_start, 0) + If(attend_C, C_end - C_start, 0)
h1 = opt.maximize(meetings_count)
h2 = opt.maximize(total_duration)

if opt.check() == sat:
    model = opt.model()
    itinerary = []
    has_R = is_true(model.evaluate(attend_R))
    has_C = is_true(model.evaluate(attend_C))
    if has_R and has_C:
        if is_true(model.evaluate(order_R_first)):
            itinerary.append({
                "action": "meet",
                "location": "Union Square",
                "person": "Richard",
                "start_time": minutes_to_time(model.evaluate(R_start).as_long()),
                "end_time": minutes_to_time(model.evaluate(R_end).as_long())
            })
            itinerary.append({
                "action": "meet",
                "location": "Presidio",
                "person": "Charles",
                "start_time": minutes_to_time(model.evaluate(C_start).as_long()),
                "end_time": minutes_to_time(model.evaluate(C_end).as_long())
            })
        else:
            itinerary.append({
                "action": "meet",
                "location": "Presidio",
                "person": "Charles",
                "start_time": minutes_to_time(model.evaluate(C_start).as_long()),
                "end_time": minutes_to_time(model.evaluate(C_end).as_long())
            })
            itinerary.append({
                "action": "meet",
                "location": "Union Square",
                "person": "Richard",
                "start_time": minutes_to_time(model.evaluate(R_start).as_long()),
                "end_time": minutes_to_time(model.evaluate(R_end).as_long())
            })
    elif has_R:
        itinerary.append({
            "action": "meet",
            "location": "Union Square",
            "person": "Richard",
            "start_time": minutes_to_time(model.evaluate(R_start).as_long()),
            "end_time": minutes_to_time(model.evaluate(R_end).as_long())
        })
    elif has_C:
        itinerary.append({
            "action": "meet",
            "location": "Presidio",
            "person": "Charles",
            "start_time": minutes_to_time(model.evaluate(C_start).as_long()),
            "end_time": minutes_to_time(model.evaluate(C_end).as_long())
        })
    result = {"itinerary": itinerary}
    print(json.dumps(result))
else:
    print(json.dumps({"itinerary": []}))