from z3 import *

def main():
    # Initialize solver
    s = Solver()

    # Time in minutes from 9:00 AM
    T0 = Int('T0')           # Departure time from Castro
    A_start = Int('A_start')  # Start time for meeting Anthony
    A_end = Int('A_end')      # End time for meeting Anthony
    L_start = Int('L_start')  # Start time for meeting Laura
    L_end = Int('L_end')      # End time for meeting Laura
    O = Int('O')              # Order: 0 for Anthony first, 1 for Laura first

    # Convert times to absolute constraints (in minutes from 9:00 AM)
    # Anthony available from 12:30 PM (210 minutes) to 2:45 PM (345 minutes)
    # Laura available from 12:15 PM (195 minutes) to 7:45 PM (645 minutes)
    s.add(A_start >= 210, A_end <= 345)
    s.add(L_start >= 195, L_end <= 645)

    # Meeting durations
    s.add(A_end == A_start + 30)  # 30 minutes for Anthony
    s.add(L_end == L_start + 75)  # 75 minutes for Laura

    # Order and travel constraints
    s.add(Or(
        And(O == 0, 
            T0 >= 0, 
            A_start >= T0 + 20,  # Travel Castro to Financial: 20 minutes
            L_start >= A_end + 17),  # Travel Financial to Mission: 17 minutes
        And(O == 1, 
            T0 >= 0, 
            L_start >= T0 + 7,    # Travel Castro to Mission: 7 minutes
            A_start >= L_end + 17)  # Travel Mission to Financial: 17 minutes
    ))

    # Check for a feasible solution
    if s.check() == sat:
        model = s.model()
        T0_val = model[T0].as_long()
        A_start_val = model[A_start].as_long()
        A_end_val = model[A_end].as_long()
        L_start_val = model[L_start].as_long()
        L_end_val = model[L_end].as_long()
        O_val = model[O].as_long()

        # Convert minutes from 9:00 AM to HH:MM format
        def to_time(minutes_since_9am):
            total_minutes = 9 * 60 + minutes_since_9am
            hours = total_minutes // 60
            minutes = total_minutes % 60
            return f"{hours:02d}:{minutes:02d}"

        A_start_str = to_time(A_start_val)
        A_end_str = to_time(A_end_val)
        L_start_str = to_time(L_start_val)
        L_end_str = to_time(L_end_val)

        # Create itinerary based on meeting order
        if O_val == 0:
            itinerary = [
                {"action": "meet", "person": "Anthony", "start_time": A_start_str, "end_time": A_end_str},
                {"action": "meet", "person": "Laura", "start_time": L_start_str, "end_time": L_end_str}
            ]
        else:
            itinerary = [
                {"action": "meet", "person": "Laura", "start_time": L_start_str, "end_time": L_end_str},
                {"action": "meet", "person": "Anthony", "start_time": A_start_str, "end_time": A_end_str}
            ]

        # Output the solution as JSON
        result = {"itinerary": itinerary}
        print("SOLUTION:")
        print(result)
    else:
        print("No solution found")

if __name__ == '__main__':
    main()