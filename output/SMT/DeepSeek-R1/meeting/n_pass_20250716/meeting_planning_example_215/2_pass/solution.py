from z3 import *

def main():
    # Locations: Bayview=0, Embarcadero=1, Richmond=2, Fisherman's Wharf=3
    loc_jason = 3  # Fisherman's Wharf
    loc_jessica = 1  # Embarcadero
    loc_sandra = 2  # Richmond District

    # Durations in minutes
    dur_jason = 30
    dur_jessica = 30
    dur_sandra = 120

    # Time windows (start_min, start_max) in minutes from 9:00 AM
    # Jason: 4:00 PM to 4:45 PM -> start between 420 and 435
    jason_window = (420, 435)
    # Jessica: 4:45 PM to 7:00 PM -> start between 465 and 570
    jessica_window = (465, 570)
    # Sandra: 6:30 PM to 9:45 PM -> start between 570 and 645
    sandra_window = (570, 645)

    # Travel matrix: [from][to]
    travel = [
        [0, 19, 25, 25],  # From Bayview (0) to [0,1,2,3]
        [21, 0, 21, 6],   # From Embarcadero (1)
        [26, 19, 0, 18],  # From Richmond (2)
        [26, 8, 18, 0]    # From Fisherman's Wharf (3)
    ]

    s = Optimize()

    # Boolean variables for meeting each friend
    meet_jason = Bool('meet_jason')
    meet_jessica = Bool('meet_jessica')
    meet_sandra = Bool('meet_sandra')

    # Start time variables (in minutes from 9:00 AM)
    jason_start = Real('jason_start')
    jessica_start = Real('jessica_start')
    sandra_start = Real('sandra_start')

    # Constraints if meeting Jason
    s.add(Implies(meet_jason, jason_start >= jason_window[0]))
    s.add(Implies(meet_jason, jason_start <= jason_window[1]))
    s.add(Implies(meet_jason, jason_start >= travel[0][loc_jason]))  # Travel from Bayview to Jason

    # Constraints if meeting Jessica
    s.add(Implies(meet_jessica, jessica_start >= jessica_window[0]))
    s.add(Implies(meet_jessica, jessica_start <= jessica_window[1]))
    s.add(Implies(meet_jessica, jessica_start >= travel[0][loc_jessica]))  # Travel from Bayview to Jessica

    # Constraints if meeting Sandra
    s.add(Implies(meet_sandra, sandra_start >= sandra_window[0]))
    s.add(Implies(meet_sandra, sandra_start <= sandra_window[1]))
    s.add(Implies(meet_sandra, sandra_start >= travel[0][loc_sandra]))  # Travel from Bayview to Sandra

    # Pairwise constraints for Jason and Jessica
    c1 = Implies(And(meet_jason, meet_jessica),
                 Or(
                     jason_start + dur_jason + travel[loc_jason][loc_jessica] <= jessica_start,
                     jessica_start + dur_jessica + travel[loc_jessica][loc_jason] <= jason_start
                 ))
    s.add(c1)

    # Pairwise constraints for Jason and Sandra
    c2 = Implies(And(meet_jason, meet_sandra),
                 Or(
                     jason_start + dur_jason + travel[loc_jason][loc_sandra] <= sandra_start,
                     sandra_start + dur_sandra + travel[loc_sandra][loc_jason] <= jason_start
                 ))
    s.add(c2)

    # Pairwise constraints for Jessica and Sandra
    c3 = Implies(And(meet_jessica, meet_sandra),
                 Or(
                     jessica_start + dur_jessica + travel[loc_jessica][loc_sandra] <= sandra_start,
                     sandra_start + dur_sandra + travel[loc_sandra][loc_jessica] <= jessica_start
                 ))
    s.add(c3)

    # Maximize the number of meetings
    total_meetings = If(meet_jason, 1, 0) + If(meet_jessica, 1, 0) + If(meet_sandra, 1, 0)
    s.maximize(total_meetings)

    # Check and get the model
    if s.check() == sat:
        model = s.model()
        met_jason = is_true(model[meet_jason])
        met_jessica = is_true(model[meet_jessica])
        met_sandra = is_true(model[meet_sandra])
        total = 0
        schedule = []

        if met_jason:
            total += 1
            start = model[jason_start]
            # Convert Z3 rational to float
            if is_rational_value(start):
                start_val = float(start.numerator_as_long()) / float(start.denominator_as_long())
            else:
                start_val = start.as_long() if is_int_value(start) else float(start.as_decimal(10))
            schedule.append(("Jason", "Fisherman's Wharf", start_val, start_val + dur_jason))

        if met_jessica:
            total += 1
            start = model[jessica_start]
            if is_rational_value(start):
                start_val = float(start.numerator_as_long()) / float(start.denominator_as_long())
            else:
                start_val = start.as_long() if is_int_value(start) else float(start.as_decimal(10))
            schedule.append(("Jessica", "Embarcadero", start_val, start_val + dur_jessica))

        if met_sandra:
            total += 1
            start = model[sandra_start]
            if is_rational_value(start):
                start_val = float(start.numerator_as_long()) / float(start.denominator_as_long())
            else:
                start_val = start.as_long() if is_int_value(start) else float(start.as_decimal(10))
            schedule.append(("Sandra", "Richmond District", start_val, start_val + dur_sandra))

        # Sort the schedule by start time
        schedule.sort(key=lambda x: x[2])

        # Format the output
        result = f"SOLUTION: Met {total} friends.\n"
        for friend, location, start, end in schedule:
            # Convert minutes to time string
            total_minutes_start = 9 * 60 + start
            hours_start = int(total_minutes_start // 60)
            minutes_start = int(total_minutes_start % 60)
            period_start = "AM" if hours_start < 12 else "PM"
            if hours_start > 12:
                hours_start -= 12
            elif hours_start == 0:
                hours_start = 12
            elif hours_start == 12:
                period_start = "PM"

            total_minutes_end = 9 * 60 + end
            hours_end = int(total_minutes_end // 60)
            minutes_end = int(total_minutes_end % 60)
            period_end = "AM" if hours_end < 12 else "PM"
            if hours_end > 12:
                hours_end -= 12
            elif hours_end == 0:
                hours_end = 12
            elif hours_end == 12:
                period_end = "PM"

            result += f"- Met {friend} at {location} from {hours_start}:{minutes_start:02d}{period_start} to {hours_end}:{minutes_end:02d}{period_end}.\n"
        print(result)
    else:
        print("SOLUTION: No feasible schedule found.")

if __name__ == "__main__":
    main()