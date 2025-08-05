from z3 import *

def min_to_time(total_minutes):
    hours = total_minutes // 60
    minutes = total_minutes % 60
    total_hours = 9 + hours
    return f"{total_hours:02d}:{minutes:02d}"

def main():
    k_start = Int('k_start')
    k_duration = Int('k_duration')
    t_start = Int('t_start')
    t_duration = Int('t_duration')
    t_end = t_start + t_duration

    opt = Optimize()
    opt.add(k_start >= 180)  # Kenneth available from 12:00 (180 minutes from 9:00)
    opt.add(k_start >= 13)   # Travel time from Nob Hill to Mission District
    opt.add(k_duration >= 45)
    opt.add(k_start + k_duration <= 405)  # Kenneth available until 15:45 (405 minutes)
    opt.add(t_start >= k_start + k_duration + 16)  # Travel time to Pacific Heights
    opt.add(t_start >= 390)  # Thomas available from 15:30 (390 minutes)
    opt.add(t_duration >= 75)
    opt.add(t_end <= 615)    # Thomas available until 19:15 (615 minutes)

    opt.minimize(t_end)

    if opt.check() == sat:
        m = opt.model()
        min_t_end = m[t_end].as_long()
        opt2 = Optimize()
        opt2.add(k_start >= 180)
        opt2.add(k_start >= 13)
        opt2.add(k_duration >= 45)
        opt2.add(k_start + k_duration <= 405)
        opt2.add(t_start >= k_start + k_duration + 16)
        opt2.add(t_start >= 390)
        opt2.add(t_duration >= 75)
        opt2.add(t_end <= 615)
        opt2.add(t_end == min_t_end)
        opt2.maximize(k_duration)
        if opt2.check() == sat:
            m2 = opt2.model()
            k_start_val = m2[k_start].as_long()
            k_duration_val = m2[k_duration].as_long()
            t_start_val = m2[t_start].as_long()
            t_duration_val = m2[t_duration].as_long()
            k_end_val = k_start_val + k_duration_val
            t_end_val = t_start_val + t_duration_val

            k_start_time = min_to_time(k_start_val)
            k_end_time = min_to_time(k_end_val)
            t_start_time = min_to_time(t_start_val)
            t_end_time = min_to_time(t_end_val)

            itinerary = [
                {"action": "meet", "person": "Kenneth", "start_time": k_start_time, "end_time": k_end_time},
                {"action": "meet", "person": "Thomas", "start_time": t_start_time, "end_time": t_end_time}
            ]
            result = {"itinerary": itinerary}
            print(f"SOLUTION: {result}")
        else:
            print("No solution found in the second optimization")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()