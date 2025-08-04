from z3 import *

def solve_scheduling():
    # Initialize the solver
    s = Solver()

    # Define variables for meeting Carol
    meet_carol_start = Int('meet_carol_start')  # in minutes from 9:00 AM
    meet_carol_duration = 60  # minimum 60 minutes

    # Define variables for meeting Jessica
    meet_jessica_start = Int('meet_jessica_start')  # in minutes from 9:00 AM
    meet_jessica_duration = 45  # minimum 45 minutes

    # Convert friend availability to minutes from 9:00 AM
    # Carol is available from 11:30 AM to 3:00 PM
    carol_start_available = (11 * 60 + 30) - (9 * 60)  # 150 minutes from 9:00 AM
    carol_end_available = (15 * 60 + 0) - (9 * 60)  # 360 minutes from 9:00 AM

    # Jessica is available from 3:30 PM to 4:45 PM
    jessica_start_available = (15 * 60 + 30) - (9 * 60)  # 390 minutes from 9:00 AM
    jessica_end_available = (16 * 60 + 45) - (9 * 60)  # 465 minutes from 9:00 AM

    # Travel times in minutes
    # From Richmond to Marina: 9 minutes
    # From Marina to Pacific Heights: 7 minutes
    # From Richmond to Pacific Heights: 10 minutes
    # From Pacific Heights to Marina: 6 minutes
    # From Marina to Richmond: 11 minutes
    # From Pacific Heights to Richmond: 12 minutes

    # Constraints for meeting Carol:
    # 1. Meeting must start within her availability window
    s.add(meet_carol_start >= carol_start_available)
    s.add(meet_carol_start + meet_carol_duration <= carol_end_available)

    # Constraints for meeting Jessica:
    # 1. Meeting must start within her availability window
    s.add(meet_jessica_start >= jessica_start_available)
    s.add(meet_jessica_start + meet_jessica_duration <= jessica_end_available)

    # Travel constraints:
    # Option 1: Meet Carol first, then Jessica
    # Travel from Marina to Pacific Heights: 7 minutes
    option1 = And(
        meet_carol_start + meet_carol_duration + 7 <= meet_jessica_start
    )

    # Option 2: Meet Jessica first, then Carol
    # But Jessica's time is after Carol's, so this is impossible
    option2 = False

    # Option 3: Meet only Carol or only Jessica
    # But we want to meet both, so we don't consider this

    s.add(Or(option1, option2))

    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        carol_start = m[meet_carol_start].as_long()
        jessica_start = m[meet_jessica_start].as_long()

        # Convert minutes back to HH:MM format from 9:00 AM
        def to_time_str(minutes):
            total_minutes = 9 * 60 + minutes
            h = total_minutes // 60
            m = total_minutes % 60
            return f"{h:02d}:{m:02d}"

        carol_start_time = to_time_str(carol_start)
        carol_end_time = to_time_str(carol_start + meet_carol_duration)
        jessica_start_time = to_time_str(jessica_start)
        jessica_end_time = to_time_str(jessica_start + meet_jessica_duration)

        itinerary = [
            {"action": "meet", "person": "Carol", "start_time": carol_start_time, "end_time": carol_end_time},
            {"action": "meet", "person": "Jessica", "start_time": jessica_start_time, "end_time": jessica_end_time}
        ]

        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Execute the solver
solution = solve_scheduling()
print(solution)