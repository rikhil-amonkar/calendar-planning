from z3 import Optimize, Int, Bool, If, And, Or, Not, Sum, is_true, sat

def minute_to_str(m):
    h = m // 60
    mn = m % 60
    return f"{h:02d}:{mn:02d}"

def solve_itinerary():
    opt = Optimize()

    # Time constants (minutes from midnight)
    BV_ARRIVAL = 9*60  # 09:00

    # Availability windows
    R_START_WIN, R_END_WIN = 8*60+45, 13*60      # Richard at Union Square 08:45-13:00
    C_START_WIN, C_END_WIN = 9*60+45, 13*60      # Charles at Presidio 09:45-13:00

    # Travel times (minutes)
    BV_to_US = 17
    BV_to_P  = 31
    US_to_P  = 24
    P_to_US  = 22

    # Variables
    r_start, r_end = Int('r_start'), Int('r_end')
    c_start, c_end = Int('c_start'), Int('c_end')
    r_dur, c_dur = Int('r_dur'), Int('c_dur')
    r_meet, c_meet = Bool('r_meet'), Bool('c_meet')
    r_first = Bool('r_first')  # If both meet, order flag

    # Durations link
    opt.add(r_dur == If(r_meet, r_end - r_start, 0))
    opt.add(c_dur == If(c_meet, c_end - c_start, 0))
    opt.add(r_dur >= 0, c_dur >= 0)

    # Window constraints if meeting
    opt.add(If(r_meet, And(r_start >= R_START_WIN, r_end <= R_END_WIN, r_end >= r_start), True))
    opt.add(If(c_meet, And(c_start >= C_START_WIN, c_end <= C_END_WIN, c_end >= c_start), True))

    # Start at Bayview at 09:00; must be able to reach first meeting
    # Case: only Richard
    only_r = And(r_meet, Not(c_meet))
    opt.add(If(only_r, r_start >= BV_ARRIVAL + BV_to_US, True))

    # Case: only Charles
    only_c = And(c_meet, Not(r_meet))
    opt.add(If(only_c, c_start >= BV_ARRIVAL + BV_to_P, True))

    # Case: both meet, enforce travel and order
    both = And(r_meet, c_meet)

    # If Richard first
    opt.add(If(And(both, r_first),
               And(
                   r_start >= BV_ARRIVAL + BV_to_US,
                   c_start >= r_end + US_to_P
               ),
               True))

    # If Charles first
    opt.add(If(And(both, Not(r_first)),
               And(
                   c_start >= BV_ARRIVAL + BV_to_P,
                   r_start >= c_end + P_to_US
               ),
               True))

    # Primary objective: maximize number of friends with at least 120 minutes
    r_sat = If(And(r_meet, r_dur >= 120), 1, 0)
    c_sat = If(And(c_meet, c_dur >= 120), 1, 0)
    opt.maximize(r_sat + c_sat)

    # Secondary objective: maximize total meeting minutes
    opt.maximize(r_dur + c_dur)

    # Tertiary: prefer earlier start (tiny nudge) to break ties consistently
    # Not strictly necessary, but helps determinism
    opt.minimize(If(r_meet, r_start, BV_ARRIVAL) + If(c_meet, c_start, BV_ARRIVAL))

    if opt.check() != sat:
        return {"itinerary": []}

    m = opt.model()

    entries = []

    # Collect meetings if they have positive duration
    if is_true(m[r_meet]) and m[r_dur].as_long() > 0:
        rs, re = m[r_start].as_long(), m[r_end].as_long()
        entries.append({
            "action": "meet",
            "person": "Richard",
            "start_time": minute_to_str(rs),
            "end_time": minute_to_str(re)
        })

    if is_true(m[c_meet]) and m[c_dur].as_long() > 0:
        cs, ce = m[c_start].as_long(), m[c_end].as_long()
        entries.append({
            "action": "meet",
            "person": "Charles",
            "start_time": minute_to_str(cs),
            "end_time": minute_to_str(ce)
        })

    # Sort chronologically by start_time
    entries.sort(key=lambda e: int(e["start_time"][:2])*60 + int(e["start_time"][3:]))

    return {"itinerary": entries}

if __name__ == "__main__":
    import json
    result = solve_itinerary()
    print(json.dumps(result))