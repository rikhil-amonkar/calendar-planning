from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define variables
    # Time variables are in minutes since 9:00 AM (540 minutes since midnight)
    # Jason's meeting start and end times (Presidio)
    jason_start = Int('jason_start')
    jason_end = Int('jason_end')
    
    # Kenneth's meeting start and end times (Marina District)
    kenneth_start = Int('kenneth_start')
    kenneth_end = Int('kenneth_end')
    
    # Travel times (fixed)
    ph_to_presidio = 11  # Pacific Heights to Presidio
    ph_to_marina = 6     # Pacific Heights to Marina District
    presidio_to_marina = 10  # Presidio to Marina District
    marina_to_presidio = 10  # Marina District to Presidio
    marina_to_ph = 7      # Marina District to Pacific Heights
    presidio_to_ph = 11   # Presidio to Pacific Heights

    # Constraints for Jason (Presidio: 10:00 AM to 4:15 PM, 90 minutes minimum)
    s.add(jason_start >= 60)  # 10:00 AM is 60 minutes after 9:00 AM
    s.add(jason_end <= 435)   # 4:15 PM is 435 minutes after 9:00 AM
    s.add(jason_end - jason_start >= 90)  # Minimum 90 minutes with Jason

    # Constraints for Kenneth (Marina District: 3:30 PM to 4:45 PM, 45 minutes minimum)
    s.add(kenneth_start >= 390)  # 3:30 PM is 390 minutes after 9:00 AM
    s.add(kenneth_end <= 465)    # 4:45 PM is 465 minutes after 9:00 AM
    s.add(kenneth_end - kenneth_start >= 45)  # Minimum 45 minutes with Kenneth

    # Travel constraints
    # Option 1: Pacific Heights -> Presidio -> Marina District
    option1 = And(
        jason_start >= ph_to_presidio,  # Travel from PH to Presidio
        kenneth_start >= jason_end + presidio_to_marina  # Travel from Presidio to Marina
    )

    # Option 2: Pacific Heights -> Marina District -> Presidio
    option2 = And(
        kenneth_start >= ph_to_marina,  # Travel from PH to Marina
        jason_start >= kenneth_end + marina_to_presidio  # Travel from Marina to Presidio
    )

    # Add disjunction of options
    s.add(Or(option1, option2))

    # Check if the problem is satisfiable
    if s.check() == sat:
        m = s.model()
        js = m.eval(jason_start).as_long()
        je = m.eval(jason_end).as_long()
        ks = m.eval(kenneth_start).as_long()
        ke = m.eval(kenneth_end).as_long()

        # Convert times back to hours and minutes
        def to_time(minutes):
            total_minutes = 540 + minutes  # 9:00 AM is 540 minutes
            hours = total_minutes // 60
            mins = total_minutes % 60
            return f"{hours}:{mins:02d}"

        print("SOLUTION:")
        print(f"Meet Jason at Presidio from {to_time(js)} to {to_time(je)} (Duration: {je - js} minutes)")
        print(f"Meet Kenneth at Marina District from {to_time(ks)} to {to_time(ke)} (Duration: {ke - ks} minutes)")
    else:
        print("No feasible schedule found.")

solve_scheduling()