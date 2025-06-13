from z3 import *

def main():
    # Define the variables
    nancy_met = Bool('nancy_met')
    mary_met = Bool('mary_met')
    jessica_met = Bool('jessica_met')
    T_n = Int('T_n')
    T_m = Int('T_m')
    T_j = Int('T_j')

    # Travel times dictionary: from location A to location B
    travel_time = {
        ('FD', 'CT'): 5,   # Financial District to Chinatown
        ('FD', 'AS'): 17,  # Financial District to Alamo Square
        ('FD', 'BV'): 19,  # Financial District to Bayview
        ('CT', 'AS'): 17,  # Chinatown to Alamo Square
        ('CT', 'BV'): 22,  # Chinatown to Bayview
        ('AS', 'CT'): 16,  # Alamo Square to Chinatown
        ('AS', 'BV'): 16,  # Alamo Square to Bayview
        ('BV', 'CT'): 18,  # Bayview to Chinatown
        ('BV', 'AS'): 16   # Bayview to Alamo Square
    }

    # Availability start times (in minutes after 9:00 AM)
    avail_start = {
        'nancy': 30,    # 9:30 AM
        'mary': 0,       # 7:00 AM, but we start at 9:00 so effective start is travel time (17 min)
        'jessica': 135   # 11:15 AM
    }

    # Availability end times (in minutes after 9:00 AM)
    avail_end = {
        'nancy': 270,   # 1:30 PM
        'mary': 720,     # 9:00 PM
        'jessica': 285   # 1:45 PM
    }

    # Minimum meeting durations (in minutes)
    durations = {
        'nancy': 90,
        'mary': 75,
        'jessica': 45
    }

    s = Optimize()

    # Individual constraints for Nancy
    s.add(Implies(nancy_met, T_n >= max(avail_start['nancy'], travel_time[('FD','CT')])))
    s.add(Implies(nancy_met, T_n + durations['nancy'] <= avail_end['nancy']))

    # Individual constraints for Mary
    s.add(Implies(mary_met, T_m >= max(avail_start['mary'], travel_time[('FD','AS')])))
    s.add(Implies(mary_met, T_m + durations['mary'] <= avail_end['mary']))

    # Individual constraints for Jessica
    s.add(Implies(jessica_met, T_j >= max(avail_start['jessica'], travel_time[('FD','BV')])))
    s.add(Implies(jessica_met, T_j + durations['jessica'] <= avail_end['jessica']))

    # Pairwise constraints: Nancy and Mary
    s.add(Implies(And(nancy_met, mary_met),
                  Or( T_n + durations['nancy'] + travel_time[('CT','AS')] <= T_m,
                      T_m + durations['mary'] + travel_time[('AS','CT')] <= T_n ))

    # Pairwise constraints: Nancy and Jessica
    s.add(Implies(And(nancy_met, jessica_met),
                  Or( T_n + durations['nancy'] + travel_time[('CT','BV')] <= T_j,
                      T_j + durations['jessica'] + travel_time[('BV','CT')] <= T_n ))

    # Pairwise constraints: Mary and Jessica
    s.add(Implies(And(mary_met, jessica_met),
                  Or( T_m + durations['mary'] + travel_time[('AS','BV')] <= T_j,
                      T_j + durations['jessica'] + travel_time[('BV','AS')] <= T_m ))

    # Maximize the total number of meetings
    total_meetings = If(nancy_met, 1, 0) + If(mary_met, 1, 0) + If(jessica_met, 1, 0)
    s.maximize(total_meetings)

    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        total_met = 0
        if is_true(m[nancy_met]):
            total_met += 1
        if is_true(m[mary_met]):
            total_met += 1
        if is_true(m[jessica_met]):
            total_met += 1

        print("SOLUTION:")
        print(f"We can meet {total_met} friends.")

        # Helper function to format time (minutes after 9:00 AM) to string
        def format_time(minutes_after_9am):
            total_minutes_from_midnight = 9 * 60 + minutes_after_9am
            hour = total_minutes_from_midnight // 60
            minute = total_minutes_from_midnight % 60
            hour12 = hour % 12
            if hour12 == 0:
                hour12 = 12
            suffix = "AM" if hour < 12 else "PM"
            return f"{hour12}:{minute:02d} {suffix}"

        # Print schedule for each friend if met
        if is_true(m[nancy_met]):
            start_n = m[T_n].as_long()
            end_n = start_n + durations['nancy']
            print(f"  Nancy: {format_time(start_n)} to {format_time(end_n)} at Chinatown")

        if is_true(m[mary_met]):
            start_m = m[T_m].as_long()
            end_m = start_m + durations['mary']
            print(f"  Mary: {format_time(start_m)} to {format_time(end_m)} at Alamo Square")

        if is_true(m[jessica_met]):
            start_j = m[T_j].as_long()
            end_j = start_j + durations['jessica']
            print(f"  Jessica: {format_time(start_j)} to {format_time(end_j)} at Bayview")
    else:
        print("SOLUTION:")
        print("No feasible schedule found.")

if __name__ == "__main__":
    main()