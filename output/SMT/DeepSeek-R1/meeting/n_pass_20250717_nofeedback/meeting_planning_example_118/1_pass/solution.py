from z3 import *

def to_time_str(minutes_since_900):
    total_minutes = 9 * 60 + minutes_since_900
    hours = total_minutes // 60
    minutes = total_minutes % 60
    return f"{hours:02d}:{minutes:02d}"

def compute_schedule2():
    opt = Optimize()
    t1 = Int('t1')
    d1 = Int('d1')
    t2 = Int('t2')
    d2 = Int('d2')

    opt.add(t1 >= 17)
    opt.add(t1 + d1 <= 240)
    opt.add(d1 >= 1)
    opt.add(t2 >= t1 + d1 + 24)
    opt.add(t2 >= 45)
    opt.add(t2 + d2 <= 240)
    opt.add(d2 >= 1)

    met_120_R = If(d1 >= 120, 1, 0)
    met_120_C = If(d2 >= 120, 1, 0)
    num_120 = met_120_R + met_120_C
    total_time = d1 + d2

    opt.maximize(num_120)
    opt.maximize(total_time)

    if opt.check() != sat:
        return None

    m = opt.model()
    t1_val = m[t1].as_long()
    d1_val = m[d1].as_long()
    t2_val = m[t2].as_long()
    d2_val = m[d2].as_long()

    start_R = to_time_str(t1_val)
    end_R = to_time_str(t1_val + d1_val)
    start_C = to_time_str(t2_val)
    end_C = to_time_str(t2_val + d2_val)

    itinerary = [
        {"action": "meet", "person": "Richard", "start_time": start_R, "end_time": end_R},
        {"action": "meet", "person": "Charles", "start_time": start_C, "end_time": end_C}
    ]

    return {
        'num_meetings': 2,
        'num_120': m.evaluate(num_120).as_long(),
        'total_time': d1_val + d2_val,
        'itinerary': itinerary
    }

def compute_schedule3():
    opt = Optimize()
    t1 = Int('t1')
    d1 = Int('d1')
    t2 = Int('t2')
    d2 = Int('d2')

    opt.add(t1 >= 45)
    opt.add(t1 + d1 <= 240)
    opt.add(d1 >= 1)
    opt.add(t2 >= t1 + d1 + 22)
    opt.add(t2 + d2 <= 240)
    opt.add(d2 >= 1)

    met_120_R = If(d2 >= 120, 1, 0)
    met_120_C = If(d1 >= 120, 1, 0)
    num_120 = met_120_R + met_120_C
    total_time = d1 + d2

    opt.maximize(num_120)
    opt.maximize(total_time)

    if opt.check() != sat:
        return None

    m = opt.model()
    t1_val = m[t1].as_long()
    d1_val = m[d1].as_long()
    t2_val = m[t2].as_long()
    d2_val = m[d2].as_long()

    start_C = to_time_str(t1_val)
    end_C = to_time_str(t1_val + d1_val)
    start_R = to_time_str(t2_val)
    end_R = to_time_str(t2_val + d2_val)

    itinerary = [
        {"action": "meet", "person": "Charles", "start_time": start_C, "end_time": end_C},
        {"action": "meet", "person": "Richard", "start_time": start_R, "end_time": end_R}
    ]

    return {
        'num_meetings': 2,
        'num_120': m.evaluate(num_120).as_long(),
        'total_time': d1_val + d2_val,
        'itinerary': itinerary
    }

def main():
    results = []

    # Schedule0: Only Richard
    itinerary0 = [{"action": "meet", "person": "Richard", "start_time": "09:17", "end_time": "13:00"}]
    s0 = {
        'num_meetings': 1,
        'num_120': 1,
        'total_time': 223,
        'itinerary': itinerary0
    }
    results.append(s0)

    # Schedule1: Only Charles
    itinerary1 = [{"action": "meet", "person": "Charles", "start_time": "09:45", "end_time": "13:00"}]
    s1 = {
        'num_meetings': 1,
        'num_120': 1,
        'total_time': 195,
        'itinerary': itinerary1
    }
    results.append(s1)

    # Schedule2: Richard then Charles
    s2 = compute_schedule2()
    if s2 is not None:
        results.append(s2)

    # Schedule3: Charles then Richard
    s3 = compute_schedule3()
    if s3 is not None:
        results.append(s3)

    # Find the best schedule: maximize num_meetings, then num_120, then total_time
    best = max(results, key=lambda x: (x['num_meetings'], x['num_120'], x['total_time']))
    print(f"SOLUTION: {best['itinerary']}")

if __name__ == '__main__':
    main()