from z3 import *

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

def main():
    # Initialize solver and optimizer
    s = Solver()
    o = Optimize()

    # Convert times to minutes from midnight
    start_time = 540  # 9:00 AM
    t_window_start = 9 * 60 + 45  # 9:45 AM
    t_window_end = 17 * 60 + 45   # 5:45 PM
    p_window_start = 18 * 60 + 30 # 6:30 PM
    p_window_end = 21 * 60 + 45   # 9:45 PM
    a_window_start = 20 * 60 + 30 # 8:30 PM
    a_window_end = 21 * 60 + 15   # 9:15 PM

    # Meeting duration in minutes
    dur_t = 120
    dur_p = 90
    dur_a = 45

    # Travel times from start location (Russian Hill)
    travel_start_to_t = 8  # Russian Hill to Embarcadero
    travel_start_to_p = 5  # Russian Hill to Nob Hill
    travel_start_to_a = 16 # Russian Hill to Mission District

    # Travel times between meeting locations
    travel_t_to_p = 10    # Embarcadero to Nob Hill
    travel_t_to_a = 20    # Embarcadero to Mission District
    travel_p_to_a = 13    # Nob Hill to Mission District

    # Integer variables for start and end times of each meeting
    start_t = Int('start_t')
    end_t = Int('end_t')
    start_p = Int('start_p')
    end_p = Int('end_p')
    start_a = Int('start_a')
    end_a = Int('end_a')

    # Boolean variables to indicate if a meeting is scheduled
    do_t = Bool('do_t')
    do_p = Bool('do_p')
    do_a = Bool('do_a')

    # Constraints for each meeting if scheduled
    s.add(Implies(do_t, start_t >= t_window_start))
    s.add(Implies(do_t, end_t <= t_window_end))
    s.add(Implies(do_t, end_t == start_t + dur_t))
    s.add(Implies(do_t, start_t >= start_time + travel_start_to_t))

    s.add(Implies(do_p, start_p >= p_window_start))
    s.add(Implies(do_p, end_p <= p_window_end))
    s.add(Implies(do_p, end_p == start_p + dur_p))
    s.add(Implies(And(do_p, Not(do_t)), start_p >= start_time + travel_start_to_p))

    s.add(Implies(do_a, start_a >= a_window_start))
    s.add(Implies(do_a, end_a <= a_window_end))
    s.add(Implies(do_a, end_a == start_a + dur_a))
    s.add(Implies(And(do_a, Not(do_t), Not(do_p)), start_a >= start_time + travel_start_to_a))

    # Travel constraints between meetings
    s.add(Implies(And(do_t, do_p), start_p >= end_t + travel_t_to_p))
    s.add(Implies(And(do_t, do_a, Not(do_p)), start_a >= end_t + travel_t_to_a))
    s.add(Implies(And(do_p, do_a), start_a >= end_p + travel_p_to_a))

    # Ensure chronological order if multiple meetings are scheduled
    s.add(Implies(And(do_t, do_p), start_t < start_p))
    s.add(Implies(And(do_t, do_a), start_t < start_a))
    s.add(Implies(And(do_p, do_a), start_p < start_a))

    # Maximize the number of meetings
    count = Int('count')
    s.add(count == If(do_t, 1, 0) + If(do_p, 1, 0) + If(do_a, 1, 0))
    o.add(s.assertions())
    o.maximize(count)

    # Check if a solution exists
    if o.check() == sat:
        m = o.model()
        itinerary = []
        if m[do_t]:
            start_val = m[start_t].as_long()
            end_val = m[end_t].as_long()
            itinerary.append({
                "action": "meet",
                "person": "Timothy",
                "start_time": minutes_to_time(start_val),
                "end_time": minutes_to_time(end_val)
            })
        if m[do_p]:
            start_val = m[start_p].as_long()
            end_val = m[end_p].as_long()
            itinerary.append({
                "action": "meet",
                "person": "Patricia",
                "start_time": minutes_to_time(start_val),
                "end_time": minutes_to_time(end_val)
            })
        if m[do_a]:
            start_val = m[start_a].as_long()
            end_val = m[end_a].as_long()
            itinerary.append({
                "action": "meet",
                "person": "Ashley",
                "start_time": minutes_to_time(start_val),
                "end_time": minutes_to_time(end_val)
            })
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: x['start_time'])
        print(f'{{"itinerary": {itinerary}}}')
    else:
        print("No solution found")

if __name__ == "__main__":
    main()