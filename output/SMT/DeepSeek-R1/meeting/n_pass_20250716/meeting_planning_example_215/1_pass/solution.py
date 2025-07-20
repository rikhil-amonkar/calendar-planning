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
        [21, 0, 21, 6],    # From Embarcadero (1)
        [26, 19, 0, 18],   # From Richmond (2)
        [26, 8, 18, 0]     # From Fisherman's Wharf (3)
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
    s.add(Implies(And(meet_jason, meet_jessica),
          Or(
              jason_start + dur_jason + travel[loc_jason][loc_jessica] <= jessica_start,
              jessica_start + dur_jessica + travel[loc_jessica][loc_jason] <= jason_start
          ))

    # Pairwise constraints for Jason and Sandra
    s.add(Implies(And(meet_jason, meet_sandra),
          Or(
              jason_start + dur_jason + travel[loc_jason][loc_sandra] <= sandra_start,
              sandra_start + dur_sandra + travel[loc_sandra][loc_jason] <= jason_start
          ))

    # Pairwise constraints for Jessica and Sandra
    s.add(Implies(And(meet_jessica, meet_sandra),
          Or(
              jessica_start + dur_jessica + travel[loc_jessica][loc_sandra] <= sandra_start,
              sandra_start + dur_sandra + travel[loc_sandra][loc_jessica] <= jessica_start
          ))

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
            start = model[jason_start].as_fraction() if isinstance(model[jason_start], RatNumRef) else model[jason_start]
            start_minutes = float(start.numerator_as_long()) / float(start.denominator_as_long()) if isinstance(start, RatNumRef) else float(start)
            schedule.append(("Jason", "Fisherman's Wharf", start_minutes, start_minutes + dur_jason))

        if met_jessica:
            total += 1
            start = model[jessica_start].as_fraction() if isinstance(model[jessica_start], RatNumRef) else model[jessica_start]
            start_minutes = float(start.numerator_as_long()) / float(start.denominator_as_long()) if isinstance(start, RatNumRef) else float(start)
            schedule.append(("Jessica", "Embarcadero", start_minutes, start_minutes + dur_jessica))

        if met_sandra:
            total += 1
            start = model[sandra_start].as_fraction() if isinstance(model[sandra_start], RatNumRef) else model[sandra_start]
            start_minutes = float(start.numerator_as_long()) / float(start.denominator_as_long()) if isinstance(start, RatNumRef) else float(start)
            schedule.append(("Sandra", "Richmond District", start_minutes, start_minutes + dur_sandra))

        # Sort the schedule by start time
        schedule.sort(key=lambda x: x[2])

        # Format the output
        result = f"SOLUTION: Met {total} friends.\n"
        for friend, location, start, end in schedule:
            # Convert minutes to time string
            start_hour = 9 + (start // 60)
            start_minute = start % 60
            start_ampm = "AM" if start_hour < 12 else "PM"
            if start_hour > 12:
                start_hour -= 12
            end_hour = 9 + (end // 60)
            end_minute = end % 60
            end_ampm = "AM" if end_hour < 12 else "PM"
            if end_hour > 12:
                end_hour -= 12
            result += f"- Met {friend} at {location} from {int(start_hour)}:{int(start_minute):02d}{start_ampm} to {int(end_hour)}:{int(end_minute):02d}{end_ampm}.\n"
        print(result)
    else:
        print("SOLUTION: No feasible schedule found.")

if __name__ == "__main__":
    main()