from z3 import *

def main():
    # Convert time to minutes since 9:00 AM
    start_barbara = (13 - 9) * 60 + 15   # 1:15 PM = 255 minutes
    end_barbara = (18 - 9) * 60 + 15      # 6:15 PM = 555 minutes
    min_meeting = 45

    # Travel time from Russian Hill to Richmond District
    rh_to_rd = 14

    # Define departure time variable T (minutes after 9:00 AM)
    T = Int('T')

    # Arrival time at Richmond
    arrival = T + rh_to_rd

    # Meeting start time: max of arrival time and Barbara's start time
    meeting_start = If(arrival >= start_barbara, arrival, start_barbara)
    meeting_end = meeting_start + min_meeting

    # Constraints
    constraints = [
        T >= 0,
        meeting_end <= end_barbara
    ]

    # Waiting time at Richmond: meeting_start - arrival
    waiting_time = meeting_start - arrival

    # Set up optimizer with objectives
    opt = Optimize()
    opt.add(constraints)
    opt.minimize(waiting_time)
    opt.maximize(T)

    if opt.check() == sat:
        m = opt.model()
        departure_time = m.eval(T).as_long()
        
        # Convert departure time to human-readable format
        total_minutes_dep = 9 * 60 + departure_time
        hours_dep = total_minutes_dep // 60
        mins_dep = total_minutes_dep % 60
        dep_period = "AM" if hours_dep < 12 else "PM"
        hours_dep_12 = hours_dep if hours_dep <= 12 else hours_dep - 12
        if hours_dep_12 == 0: hours_dep_12 = 12
        departure_str = f"{hours_dep_12}:{mins_dep:02d} {dep_period}" if hours_dep < 12 or hours_dep >= 13 else f"{hours_dep}:{mins_dep:02d} {dep_period}"
        
        # Convert arrival time to human-readable format
        arrival_time_val = departure_time + rh_to_rd
        total_minutes_arr = 9 * 60 + arrival_time_val
        hours_arr = total_minutes_arr // 60
        mins_arr = total_minutes_arr % 60
        arr_period = "AM" if hours_arr < 12 else "PM"
        hours_arr_12 = hours_arr if hours_arr <= 12 else hours_arr - 12
        if hours_arr_12 == 0: hours_arr_12 = 12
        arrival_str = f"{hours_arr_12}:{mins_arr:02d} {arr_period}" if hours_arr < 12 or hours_arr >= 13 else f"{hours_arr}:{mins_arr:02d} {arr_period}"
        
        # Convert meeting start and end times
        meeting_start_val = max(arrival_time_val, start_barbara)
        meeting_end_val = meeting_start_val + min_meeting
        
        total_minutes_start = 9 * 60 + meeting_start_val
        hours_start = total_minutes_start // 60
        mins_start = total_minutes_start % 60
        start_period = "AM" if hours_start < 12 else "PM"
        hours_start_12 = hours_start if hours_start <= 12 else hours_start - 12
        if hours_start_12 == 0: hours_start_12 = 12
        start_str = f"{hours_start_12}:{mins_start:02d} {start_period}" if hours_start < 12 or hours_start >= 13 else f"{hours_start}:{mins_start:02d} {start_period}"
        
        total_minutes_end = 9 * 60 + meeting_end_val
        hours_end = total_minutes_end // 60
        mins_end = total_minutes_end % 60
        end_period = "AM" if hours_end < 12 else "PM"
        hours_end_12 = hours_end if hours_end <= 12 else hours_end - 12
        if hours_end_12 == 0: hours_end_12 = 12
        end_str = f"{hours_end_12}:{mins_end:02d} {end_period}" if hours_end < 12 or hours_end >= 13 else f"{hours_end}:{mins_end:02d} {end_period}"
        
        print("Optimal schedule:")
        print(f"Depart Russian Hill at {departure_str}.")
        print(f"Arrive at Richmond District at {arrival_str}.")
        print(f"Meet Barbara from {start_str} to {end_str}.")
    else:
        print("No valid schedule found.")

if __name__ == '__main__':
    main()