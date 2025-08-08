from z3 import *

def main():
    # Total available time from 9:00 AM to 1:00 PM in minutes (240 minutes)
    total_time = 240

    # Define variables
    option = Int('option')  # 0: R then C, 1: C then R, 2: only R, 3: only C
    dur_R = Int('dur_R')     # Duration with Richard
    dur_C = Int('dur_C')     # Duration with Charles
    start_R = Int('start_R') # Start time with Richard (minutes from 9:00)
    start_C = Int('start_C') # Start time with Charles (minutes from 9:00)

    s = Optimize()

    # Define constraints for each option
    s.add(Or(option == 0, option == 1, option == 2, option == 3))
    s.add(dur_R >= 0, dur_C >= 0)

    # Option 0: Richard then Charles
    s.add(If(option == 0,
             And(
                 start_R == 17,
                 start_C == If(17 + dur_R + 24 >= 45, 17 + dur_R + 24, 45),
                 start_C + dur_C <= total_time
             ),
             True))

    # Option 1: Charles then Richard
    s.add(If(option == 1,
             And(
                 start_C == 45,
                 start_R == 45 + dur_C + 22,
                 start_R + dur_R <= total_time
             ),
             True))

    # Option 2: only Richard
    s.add(If(option == 2,
             And(
                 start_R == 17,
                 dur_C == 0,
                 start_R + dur_R <= total_time,
                 start_C == 0  # Dummy value
             ),
             True))

    # Option 3: only Charles
    s.add(If(option == 3,
             And(
                 start_C == 45,
                 dur_R == 0,
                 start_C + dur_C <= total_time,
                 start_R == 0  # Dummy value
             ),
             True))

    # Define met_R and met_C based on duration constraints
    met_R = If(dur_R >= 120, 1, 0)
    met_C = If(dur_C >= 120, 1, 0)
    count = met_R + met_C

    # Maximize the number of friends met
    s.maximize(count)

    # Check for a solution
    if s.check() == sat:
        m = s.model()
        dur_R_val = m[dur_R].as_long()
        dur_C_val = m[dur_C].as_long()
        start_R_val = m[start_R].as_long()
        start_C_val = m[start_C].as_long()

        # Convert minutes to HH:MM format
        def to_time(minutes):
            total_minutes = minutes
            hours = 9 + total_minutes // 60
            minutes = total_minutes % 60
            return f"{hours:02d}:{minutes:02d}"

        itinerary = []
        if dur_R_val >= 120:
            start_str = to_time(start_R_val)
            end_str = to_time(start_R_val + dur_R_val)
            itinerary.append({
                "action": "meet",
                "person": "Richard",
                "start_time": start_str,
                "end_time": end_str
            })
        if dur_C_val >= 120:
            start_str = to_time(start_C_val)
            end_str = to_time(start_C_val + dur_C_val)
            itinerary.append({
                "action": "meet",
                "person": "Charles",
                "start_time": start_str,
                "end_time": end_str
            })

        # Output the solution
        print({
            "itinerary": itinerary
        })
    else:
        print('No solution found')

if __name__ == "__main__":
    main()