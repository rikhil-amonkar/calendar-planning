from z3 import *

def main():
    # Define the variables
    T0 = Int('T0')        # Time leaving The Castro (minutes after 9:00 AM)
    A_start = Int('A_start')  # Start time for meeting with Anthony
    A_end = Int('A_end')      # End time for meeting with Anthony
    L_start = Int('L_start')  # Start time for meeting with Laura
    L_end = Int('L_end')      # End time for meeting with Laura
    order = Bool('order')   # True: Anthony first, False: Laura first

    s = Solver()

    # Constraints for both orders
    order1_constraints = And(
        T0 >= 0,
        A_start >= T0 + 20,      # Travel from Castro to Financial District takes 20 minutes
        A_start >= 210,           # Anthony available from 12:30 PM (210 minutes after 9:00 AM)
        A_end == A_start + 30,    # Meet Anthony for exactly 30 minutes
        A_end <= 345,             # Anthony must leave by 2:45 PM (345 minutes)
        L_start >= A_end + 17,    # Travel from Financial to Mission District takes 17 minutes
        L_start >= 195,           # Laura available from 12:15 PM (195 minutes)
        L_end == L_start + 75,    # Meet Laura for exactly 75 minutes
        L_end <= 645              # Laura must leave by 7:45 PM (645 minutes)
    )

    order2_constraints = And(
        T0 >= 0,
        L_start >= T0 + 7,        # Travel from Castro to Mission District takes 7 minutes
        L_start >= 195,            # Laura available from 12:15 PM (195 minutes)
        L_end == L_start + 75,    # Meet Laura for exactly 75 minutes
        L_end <= 645,             # Laura must leave by 7:45 PM (645 minutes)
        A_start >= L_end + 17,    # Travel from Mission to Financial District takes 17 minutes
        A_start >= 210,            # Anthony available from 12:30 PM (210 minutes)
        A_end == A_start + 30,    # Meet Anthony for exactly 30 minutes
        A_end <= 345              # Anthony must leave by 2:45 PM (345 minutes)
    )

    s.add(Or(And(order, order1_constraints), And(Not(order), order2_constraints)))

    if s.check() == sat:
        m = s.model()
        T0_val = m.eval(T0).as_long()
        A_start_val = m.eval(A_start).as_long()
        A_end_val = m.eval(A_end).as_long()
        L_start_val = m.eval(L_start).as_long()
        L_end_val = m.eval(L_end).as_long()
        order_val = is_true(m.eval(order))

        def min_to_time(mins):
            total_minutes = 9 * 60 + mins
            hours = total_minutes // 60
            minutes = total_minutes % 60
            am_pm = "AM" if hours < 12 else "PM"
            hours12 = hours % 12
            if hours12 == 0:
                hours12 = 12
            return f"{hours12}:{minutes:02d} {am_pm}"

        if order_val:
            print("Order: Meet Anthony first, then Laura.")
            print(f"Leave The Castro at {min_to_time(T0_val)}")
            print(f"Meet Anthony in Financial District from {min_to_time(A_start_val)} to {min_to_time(A_end_val)}")
            print(f"Travel to Mission District (17 minutes), arriving at {min_to_time(A_end_val + 17)}")
            print(f"Meet Laura in Mission District from {min_to_time(L_start_val)} to {min_to_time(L_end_val)}")
        else:
            print("Order: Meet Laura first, then Anthony.")
            print(f"Leave The Castro at {min_to_time(T0_val)}")
            print(f"Meet Laura in Mission District from {min_to_time(L_start_val)} to {min_to_time(L_end_val)}")
            print(f"Travel to Financial District (17 minutes), arriving at {min_to_time(L_end_val + 17)}")
            print(f"Meet Anthony in Financial District from {min_to_time(A_start_val)} to {min_to_time(A_end_val)}")
    else:
        print("No feasible schedule found.")

if __name__ == "__main__":
    main()