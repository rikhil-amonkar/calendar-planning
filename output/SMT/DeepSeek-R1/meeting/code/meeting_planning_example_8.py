from z3 import *

def main():
    # Time in minutes after 9:00 AM
    T_depart = Int('T_depart')  # Departure time from Chinatown
    T_start = Int('T_start')    # Start time of meeting
    T_end = Int('T_end')        # End time of meeting

    opt = Optimize()
    opt.add(T_depart >= 0)
    opt.add(T_start >= T_depart + 12)  # Travel time to Marina District
    opt.add(T_start >= -60)            # Stephanie available from 8AM (9AM -60 mins)
    opt.add(T_end <= 360)              # Stephanie available until 3PM (9AM + 360 mins)
    opt.add(T_end - T_start >= 105)    # Minimum meeting duration
    opt.minimize(T_end)                # Optimize for earliest possible end

    if opt.check() == sat:
        m = opt.model()
        depart = m.eval(T_depart).as_long()
        start = m.eval(T_start).as_long()
        end = m.eval(T_end).as_long()

        def time_str(mins):
            total_mins = 9 * 60 + mins
            hours, mins = divmod(total_mins, 60)
            am_pm = "AM" if hours < 12 else "PM"
            hours = hours if hours >= 1 and hours <= 12 else abs(hours - 12)
            return f"{hours}:{mins:02d}{am_pm}"

        print(f"Depart Chinatown at {time_str(depart)}")
        print(f"Arrive Marina District at {time_str(depart + 12)}")
        print(f"Meet Stephanie from {time_str(start)} to {time_str(end)}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()