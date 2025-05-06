from z3 import *

def main():
    # Initialize the optimizer
    opt = Optimize()

    # Convert times to minutes since midnight
    pacific_heights_departure = 9 * 60  # 9:00 AM

    # Jason's availability at Presidio: 10:00 AM to 4:15 PM
    jason_available_start = 10 * 60
    jason_available_end = 16 * 60 + 15

    # Kenneth's availability at Marina: 3:30 PM to 4:45 PM
    kenneth_available_start = 15 * 60 + 30
    kenneth_available_end = 16 * 60 + 45

    # Meeting duration constraints
    jason_min_duration = 90
    kenneth_min_duration = 45

    # Variables for meeting start and end times
    jason_start = Int('jason_start')
    jason_end = Int('jason_end')
    kenneth_start = Int('kenneth_start')
    kenneth_end = Int('kenneth_end')

    # Boolean flags for whether meetings are scheduled
    jason_met = Bool('jason_met')
    kenneth_met = Bool('kenneth_met')

    # Constraints for Jason's meeting
    opt.add(Implies(jason_met, And(
        jason_start >= jason_available_start,
        jason_end <= jason_available_end,
        jason_end >= jason_start + jason_min_duration,
        # Travel from Pacific Heights to Presidio (11 minutes)
        jason_start >= pacific_heights_departure + 11
    )))

    # Constraints for Kenneth's meeting
    # Arrival time depends on whether Jason was met first
    arrival_at_marina = If(jason_met, jason_end + 10, pacific_heights_departure + 6)
    opt.add(Implies(kenneth_met, And(
        kenneth_start >= arrival_at_marina,
        kenneth_start >= kenneth_available_start,
        kenneth_end <= kenneth_available_end,
        kenneth_end >= kenneth_start + kenneth_min_duration
    )))

    # Maximize the number of friends met
    opt.maximize(If(jason_met, 1, 0) + If(kenneth_met, 1, 0))

    if opt.check() == sat:
        m = opt.model()
        print(f"Jason: {'Met' if m.eval(jason_met) else 'Not met'}")
        print(f"Kenneth: {'Met' if m.eval(kenneth_met) else 'Not met'}")
    else:
        print("No valid schedule found")

if __name__ == "__main__":
    main()