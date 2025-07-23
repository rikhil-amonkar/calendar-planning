from z3 import *
import json

def min_to_time(mins):
    base_hour = 9
    total_hours = base_hour + (mins // 60)
    hours_part = total_hours
    minutes_part = mins % 60
    return f"{hours_part:02d}:{minutes_part:02d}"

def main():
    k_start = Int('k_start')
    k_duration = Int('k_duration')
    k_end = k_start + k_duration
    t_start = Int('t_start')
    t_duration = Int('t_duration')
    t_end = t_start + t_duration

    opt1 = Optimize()
    opt1.add(k_start >= 180)
    opt1.add(k_duration >= 45)
    opt1.add(k_end <= 405)
    opt1.add(t_start >= k_end + 16)
    opt1.add(t_start >= 390)
    opt1.add(t_duration >= 75)
    opt1.add(t_end <= 615)
    opt1.minimize(t_end)

    if opt1.check() == sat:
        m1 = opt1.model()
        min_t_end = m1.evaluate(t_end).as_long()

        opt2 = Optimize()
        opt2.add(k_start >= 180)
        opt2.add(k_duration >= 45)
        opt2.add(k_end <= 405)
        opt2.add(t_start >= k_end + 16)
        opt2.add(t_start >= 390)
        opt2.add(t_duration >= 75)
        opt2.add(t_end <= 615)
        opt2.add(t_end == min_t_end)
        opt2.minimize(k_duration + t_duration)

        if opt2.check() == sat:
            m2 = opt2.model()
            k_start_val = m2[k_start].as_long()
            k_duration_val = m2[k_duration].as_long()
            k_end_val = k_start_val + k_duration_val
            t_start_val = m2[t_start].as_long()
            t_duration_val = m2[t_duration].as_long()
            t_end_val = t_start_val + t_duration_val

            itinerary = [
                {"action": "meet", "person": "Kenneth", "start_time": min_to_time(k_start_val), "end_time": min_to_time(k_end_val)},
                {"action": "meet", "person": "Thomas", "start_time": min_to_time(t_start_val), "end_time": min_to_time(t_end_val)}
            ]
            result = {"itinerary": itinerary}
            print("SOLUTION: " + json.dumps(result))
        else:
            print("SOLUTION: No solution found in the second optimization step.")
    else:
        print("SOLUTION: No solution found in the first optimization step.")

if __name__ == "__main__":
    main()